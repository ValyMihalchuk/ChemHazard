
/-!
  Basic.lean

  Two running examples:
  1. Acid dilution as a sourced order-sensitive hazard.
  2. ELISA stop-solution as a protocol-specific concentration policy.

  Safety is checked before each transfer against the destination's
  current symbolic state.
-/

namespace ChemHazard

/-! ## 1. Substance ontology -/

/-- Curated hazard classes used in the examples. -/
inductive HClass
  | strongAcid
  | peroxide
  | aqueous
  | organic
  | inert
  deriving DecidableEq, Repr

/-- Coarse concentration buckets. -/
inductive Conc
  | dilute
  | moderate
  | concentrated
  deriving DecidableEq, Repr

/-- Order on concentration buckets. -/
def Conc.le : Conc → Conc → Bool
  | .dilute,       _              => true
  | .moderate,     .dilute        => false
  | .moderate,     _              => true
  | .concentrated, .concentrated  => true
  | .concentrated, _              => false

structure Substance where
  hclass : HClass
  conc   : Conc
  deriving DecidableEq, Repr

/-! ## 2. Vessel state and mixtures -/

abbrev Vessel := Nat
abbrev Mixture := List Substance

def Mixture.hasClass (m : Mixture) (c : HClass) : Bool := m.any (fun s => decide (s.hclass = c))

def Mixture.hasClassAtLeast (m : Mixture) (c : HClass) (threshold : Conc) : Bool :=
  m.any (fun s => decide (s.hclass = c) && Conc.le threshold s.conc)

/-! ## 3. Protocol model -/

structure Transfer where
  subst  : Substance
  amount : Nat
  dst    : Vessel
  deriving Repr

abbrev Protocol := List Transfer

def State := Vessel → Mixture

def State.empty : State := fun _ => []

def State.apply (σ : State) (t : Transfer) : State :=
  fun v => if v = t.dst then t.subst :: σ v else σ v

/-! ## 4. Core guard -/

/--
Blocks adding an aqueous transfer into a vessel that already contains
concentrated acid. This models the standard acid-dilution rule:
add acid to water, not water to acid.
-/
def waterIntoConcAcidGuard (t : Transfer) (m : Mixture) : Bool :=
  let addingAqueous := decide (t.subst.hclass = HClass.aqueous)
  let destHasConcAcid := m.hasClassAtLeast HClass.strongAcid Conc.concentrated
  ! (addingAqueous && destHasConcAcid)

/-- Per-step protocol check. -/
def guard (t : Transfer) (m : Mixture) : Bool :=
  waterIntoConcAcidGuard t m

def guardAll : State → Protocol → Bool
  | _, []        => true
  | σ, t :: rest => guard t (σ t.dst) && guardAll (σ.apply t) rest

def Safe (p : Protocol) : Bool := guardAll State.empty p

/-! ## 5. Example 1 — Acid dilution -/

def h2so4_conc : Substance := ⟨HClass.strongAcid, Conc.concentrated⟩
def water      : Substance := ⟨HClass.aqueous,    Conc.dilute⟩


/-- Accepted by the core dilution guard. -/
def acidDilutionSafe : Protocol :=
  [ ⟨water,      30, 0⟩,
    ⟨h2so4_conc, 10, 0⟩ ]

/-- Rejected by the core dilution guard. -/
def acidDilutionUnsafe : Protocol :=
  [ ⟨h2so4_conc, 10, 0⟩,
    ⟨water,      30, 0⟩ ]

example : Safe acidDilutionSafe = true := by decide
example : Safe acidDilutionUnsafe = false := by decide

/-! ## 6. Example 2 — ELISA stop solution -/

def tmb_peroxide_dilute : Substance := ⟨HClass.peroxide,   Conc.dilute⟩
def h2so4_dilute        : Substance := ⟨HClass.strongAcid, Conc.dilute⟩
def buffer              : Substance := ⟨HClass.aqueous,    Conc.dilute⟩

def elisaSafe : Protocol :=
  [ ⟨buffer,              50, 1⟩,
    ⟨tmb_peroxide_dilute, 20, 1⟩,
    ⟨h2so4_dilute,        50, 1⟩ ]

def elisaUnsafePerturbed : Protocol :=
  [ ⟨buffer,              50, 1⟩,
    ⟨tmb_peroxide_dilute, 20, 1⟩,
    ⟨h2so4_conc,          50, 1⟩ ]

example : Safe elisaSafe = true := by decide

/--
The core dilution guard does not reject this perturbation. That
motivates a protocol-specific extension.
-/
example : Safe elisaUnsafePerturbed = true := by decide

/-! ## 7. ELISA-specific extension -/

/--
Protocol-specific policy: do not add concentrated acid into a vessel
that already contains peroxide.
-/
def tightAcidIntoPeroxideGuard (t : Transfer) (m : Mixture) : Bool :=
  let addingConcAcid :=
    decide (t.subst.hclass = HClass.strongAcid)
    && decide (t.subst.conc = Conc.concentrated)
  let destHasAnyPeroxide := m.hasClass HClass.peroxide
  ! (addingConcAcid && destHasAnyPeroxide)

def tightGuard (t : Transfer) (m : Mixture) : Bool :=
  guard t m && tightAcidIntoPeroxideGuard t m

def tightGuardAll : State → Protocol → Bool
  | _, []        => true
  | σ, t :: rest => tightGuard t (σ t.dst) && tightGuardAll (σ.apply t) rest

def TightSafe (p : Protocol) : Bool := tightGuardAll State.empty p

example : TightSafe elisaSafe = true := by decide
example : TightSafe elisaUnsafePerturbed = false := by decide
example : TightSafe acidDilutionSafe = true := by decide
example : TightSafe acidDilutionUnsafe = false := by decide

/-! ## 8. Compositional theorem -/

def Protocol.dstVessels : Protocol → List Vessel
  | []      => []
  | t :: ts => t.dst :: Protocol.dstVessels ts

def Protocol.untouched (v : Vessel) : Protocol → Prop
  | []      => True
  | t :: ts => v ≠ t.dst ∧ Protocol.untouched v ts

def Protocol.disjointFrom (q : Protocol) (V : List Vessel) : Prop :=
  ∀ v, v ∈ V → Protocol.untouched v q

theorem State.apply_other (σ : State) (t : Transfer) (v : Vessel) (h : v ≠ t.dst) :
    (σ.apply t) v = σ v := by
  unfold State.apply
  simp [h]

/-- State after executing a protocol from left to right. -/
def runLeft : State → Protocol → State
  | σ, []      => σ
  | σ, t :: ts => runLeft (σ.apply t) ts

/-- A vessel is either untouched or appears as a destination. -/
theorem untouched_or_mem (p : Protocol) (v : Vessel) :
  Protocol.untouched v p ∨ v ∈ Protocol.dstVessels p := by
  induction p with
  | nil => exact Or.inl trivial
  | cons t ts ih =>
    unfold Protocol.untouched Protocol.dstVessels
    if h_eq : v = t.dst then
      exact Or.inr (by simp [h_eq])
    else
      cases ih with
      | inl h_unt => exact Or.inl ⟨h_eq, h_unt⟩
      | inr h_mem => exact Or.inr (by simp [h_mem])

/-- Split disjointness across the head of a protocol. -/
theorem disjointFrom_cons {t : Transfer} {ts : Protocol} {V : List Vessel}
  (h : Protocol.disjointFrom (t :: ts) V) :
  (∀ v, v ∈ V → v ≠ t.dst) ∧ Protocol.disjointFrom ts V := by
  constructor
  · intro v hv; exact (h v hv).1
  · intro v hv; exact (h v hv).2

/-- Disjoint destinations remain untouched. -/
theorem untouched_of_disjoint_dst (p : Protocol) (t : Transfer)
  (h : ∀ v, v ∈ Protocol.dstVessels p → v ≠ t.dst) :
  Protocol.untouched t.dst p := by
  cases untouched_or_mem p t.dst with
  | inl h_unt => exact h_unt
  | inr h_mem => exact False.elim (h t.dst h_mem rfl)

/-- Transfers on different destinations commute. -/
theorem state_apply_commute (σ : State) (t1 t2 : Transfer) (h : t1.dst ≠ t2.dst) :
  (σ.apply t1).apply t2 = (σ.apply t2).apply t1 := by
  funext v
  unfold State.apply
  if h1 : v = t1.dst then
    have h2 : v ≠ t2.dst := fun h_eq => h (h1.symm.trans h_eq)
    simp [h1]
    grind
  else if h2 : v = t2.dst then
    simp [h2]
    grind
  else
    simp [h1, h2]

/-- Running a protocol preserves untouched vessels. -/
theorem runLeft_eq_of_untouched (σ : State) (p : Protocol) (v : Vessel)
  (h : Protocol.untouched v p) : runLeft σ p v = σ v := by
  induction p generalizing σ with
  | nil => rfl
  | cons t ts ih =>
    unfold runLeft
    rw [ih (σ.apply t) h.2]
    exact State.apply_other σ t v h.1

/-- An untouched destination commutes with protocol execution. -/
theorem runLeft_apply_commute (σ : State) (p : Protocol) (t : Transfer)
  (h : Protocol.untouched t.dst p) :
  runLeft (σ.apply t) p = (runLeft σ p).apply t := by
  induction p generalizing σ with
  | nil => rfl
  | cons t' ts ih =>
    unfold runLeft
    rw [state_apply_commute σ t t' h.1]
    rw [ih (σ.apply t') h.2]

/-- Disjoint suffixes see the same guard conditions. -/
theorem guardAll_runLeft_eq (q : Protocol) (σ : State) (p : Protocol)
  (h_disj : Protocol.disjointFrom q (Protocol.dstVessels p)) :
  guardAll (runLeft σ p) q = guardAll σ q := by
  induction q generalizing σ with
  | nil => rfl
  | cons t ts ih =>
    unfold guardAll
    have h_split := disjointFrom_cons h_disj
    have h_unt_t := untouched_of_disjoint_dst p t h_split.1
    rw [runLeft_eq_of_untouched σ p t.dst h_unt_t]
    rw [← runLeft_apply_commute σ p t h_unt_t]
    rw [ih (σ.apply t) h_split.2]

/-- Guard evaluation over append. -/
theorem guardAll_append (σ : State) (p q : Protocol) :
  guardAll σ (p ++ q) = (guardAll σ p && guardAll (runLeft σ p) q) := by
  induction p generalizing σ with
  | nil =>
    unfold guardAll runLeft
    grind
  | cons t ts ih =>
    calc
      guardAll σ ((t :: ts) ++ q)
        = (guard t (σ t.dst) && guardAll (σ.apply t) (ts ++ q)) := rfl
      _ = (guard t (σ t.dst) && (guardAll (σ.apply t) ts && guardAll (runLeft (σ.apply t) ts) q)) := by rw [ih]
      _ = ((guard t (σ t.dst) && guardAll (σ.apply t) ts) && guardAll (runLeft (σ.apply t) ts) q) := by grind
      _ = (guardAll σ (t :: ts) && guardAll (runLeft σ (t :: ts)) q) := rfl

/-- Safe disjoint protocols remain safe after concatenation. -/
theorem guardAll_append_of_disjoint
    (p q : Protocol)
    (hSafeP : guardAll State.empty p = true)
    (hSafeQ : guardAll State.empty q = true)
    (hDisj  : q.disjointFrom p.dstVessels) :
    guardAll State.empty (p ++ q) = true := by
  rw [guardAll_append]
  have h_q := guardAll_runLeft_eq q State.empty p hDisj
  rw [h_q]
  rw [hSafeP, hSafeQ]
  rfl

end ChemHazard
