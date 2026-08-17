import Mathlib

open scoped BigOperators

namespace AlloyIsing

/-!
# Binary alloy → Ising model

We formalize a finite binary alloy with species A/B
and prove that its Hamiltonian is exactly an Ising Hamiltonian.
-/

/-- The two possible species occupying a lattice site. -/
inductive Species
  | A
  | B
  deriving DecidableEq, Repr

/-- Occupation number n_A ∈ {0,1}. -/
def nA : Species → ℝ
  | .A => 1
  | .B => 0

/-- Occupation number n_B ∈ {0,1}. -/
def nB : Species → ℝ
  | .A => 0
  | .B => 1

/-- Spin representation:
    A ↦ +1,
    B ↦ -1.
-/
def spin : Species → ℝ
  | .A => 1
  | .B => -1

@[simp]
theorem nA_eq_spin (x : Species) :
    nA x = (1 + spin x) / 2 := by
  cases x <;> norm_num [nA, spin]

@[simp]
theorem nB_eq_spin (x : Species) :
    nB x = (1 - spin x) / 2 := by
  cases x <;> norm_num [nB, spin]

@[simp]
theorem spin_sq (x : Species) :
    spin x ^ 2 = 1 := by
  cases x <;> norm_num [spin]

@[simp]
theorem nA_add_nB (x : Species) :
    nA x + nB x = 1 := by
  cases x <;> norm_num [nA, nB]


section FiniteLattice

variable {Site : Type*} [Fintype Site]

/-- A configuration of the alloy. -/
abbrev Config (Site : Type*) := Site → Species

/-- The spin configuration associated to an alloy configuration. -/
def spinConfig (σ : Config Site) : Site → ℝ :=
  fun r => spin (σ r)


/-! ## Original alloy Hamiltonian -/

/--
The original binary-alloy Hamiltonian

H =
  Σ_{r,r'} [
    J_AA(r,r') n_A(r)n_A(r')
    + J_BB(r,r') n_B(r)n_B(r')
    + J_AB(r,r') n_A(r)n_B(r')
    + J_AB(r,r') n_B(r)n_A(r')
  ].
-/
def alloyHamiltonian
    (JAA JBB JAB : Site → Site → ℝ)
    (σ : Config Site) : ℝ :=
  ∑ r : Site,
    ∑ r' : Site,
      (
        JAA r r' * nA (σ r) * nA (σ r')
        + JBB r r' * nB (σ r) * nB (σ r')
        + JAB r r' * nA (σ r) * nB (σ r')
        + JAB r r' * nB (σ r) * nA (σ r')
      )


/-! ## Effective Ising parameters -/

/--
Effective Ising coupling

J(r,r') = 1/4 (J_AA + J_BB - 2 J_AB).
-/
noncomputable def effectiveCoupling
    (JAA JBB JAB : Site → Site → ℝ)
    (r r' : Site) : ℝ :=
  (1 / 4 : ℝ) *
    (JAA r r' + JBB r r' - 2 * JAB r r')

/--
Effective magnetic field.

This is written as two sums because this form is convenient
for the proof.  Below we prove that it is identical to

1/4 Σ_{r'} [
  J_AA(r,r') - J_BB(r,r')
  + J_AA(r',r) - J_BB(r',r)
].
-/
noncomputable def effectiveField
    (JAA JBB : Site → Site → ℝ)
    (r : Site) : ℝ :=
    (∑ r' : Site,
      (1 / 4 : ℝ) * (JAA r r' - JBB r r'))
  + (∑ r' : Site,
      (1 / 4 : ℝ) * (JAA r' r - JBB r' r))

/--
The configuration-independent constant C.
-/
noncomputable def effectiveConstant
    (JAA JBB JAB : Site → Site → ℝ) : ℝ :=
  ∑ r : Site, ∑ r' : Site,
    (1 / 4 : ℝ) *
      (JAA r r' + JBB r r' + 2 * JAB r r')

/--
Generic Ising Hamiltonian, following the sign convention
used in the problem:

H = Σ J(r,r') s(r)s(r') + Σ h(r)s(r) + C.
-/
def isingHamiltonian
    (J : Site → Site → ℝ)
    (h : Site → ℝ)
    (C : ℝ)
    (s : Site → ℝ) : ℝ :=
    (∑ r : Site, ∑ r' : Site,
      J r r' * s r * s r')
  + (∑ r : Site, h r * s r)
  + C


/-! ## Local algebraic identity -/

/--
This is the algebraic calculation performed in the handwritten
solution, but reduced to a theorem about five real numbers.

It is the key local identity behind the alloy → Ising mapping.
-/
lemma pair_energy_identity
    (a b c : ℝ)
    (x y : Species) :
      a * nA x * nA y
    + b * nB x * nB y
    + c * nA x * nB y
    + c * nB x * nA y
    =
      ((1 / 4 : ℝ) * (a + b - 2 * c))
        * spin x * spin y
    + ((1 / 4 : ℝ) * (a - b))
        * (spin x + spin y)
    + ((1 / 4 : ℝ) * (a + b + 2 * c)) := by
  simp only [nA_eq_spin, nB_eq_spin]
  ring


/-! ## Rearranging the linear term -/

/--
Rearrange

Σ_{r,r'} 1/4 D(r,r') (s(r) + s(r'))

into

Σ_r h(r) s(r),

where

h(r) =
  Σ_{r'} 1/4 D(r,r')
  + Σ_{r'} 1/4 D(r',r).
-/
lemma field_rearrangement
    (D : Site → Site → ℝ)
    (s : Site → ℝ) :
    (∑ r : Site, ∑ r' : Site,
      (1 / 4 : ℝ) * D r r' * (s r + s r'))
    =
    ∑ r : Site,
      ((∑ r' : Site,
          (1 / 4 : ℝ) * D r r')
       +
       (∑ r' : Site,
          (1 / 4 : ℝ) * D r' r))
      * s r := by
  classical
  have hswap :
      (∑ r : Site, ∑ r' : Site,
        (1 / 4 : ℝ) * D r r' * s r')
      =
      ∑ r : Site, ∑ r' : Site,
        (1 / 4 : ℝ) * D r' r * s r := by
    rw [Finset.sum_comm]
  calc
    (∑ r : Site, ∑ r' : Site,
      (1 / 4 : ℝ) * D r r' * (s r + s r'))
        =
        (∑ r : Site, ∑ r' : Site,
          (1 / 4 : ℝ) * D r r' * s r)
        +
        (∑ r : Site, ∑ r' : Site,
          (1 / 4 : ℝ) * D r r' * s r') := by
            simp only [mul_add, Finset.sum_add_distrib]
    _ =
        (∑ r : Site, ∑ r' : Site,
          (1 / 4 : ℝ) * D r r' * s r)
        +
        (∑ r : Site, ∑ r' : Site,
          (1 / 4 : ℝ) * D r' r * s r) := by
            rw [hswap]
    _ =
        ∑ r : Site,
          ((∑ r' : Site,
              (1 / 4 : ℝ) * D r r')
           +
           (∑ r' : Site,
              (1 / 4 : ℝ) * D r' r))
          * s r := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro r _
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            ring


/-! ## The decomposition theorem -/

/--
First version of the main calculation:
the alloy Hamiltonian decomposes into

1. quadratic Ising term,
2. linear term,
3. constant term.
-/
lemma alloy_decomposition
    (JAA JBB JAB : Site → Site → ℝ)
    (σ : Config Site) :
    alloyHamiltonian JAA JBB JAB σ
    =
      (∑ r : Site, ∑ r' : Site,
        effectiveCoupling JAA JBB JAB r r'
          * spinConfig σ r
          * spinConfig σ r')
      +
      (∑ r : Site, ∑ r' : Site,
        (1 / 4 : ℝ)
          * (JAA r r' - JBB r r')
          * (spinConfig σ r + spinConfig σ r'))
      +
      effectiveConstant JAA JBB JAB := by
  classical
  unfold alloyHamiltonian
    effectiveCoupling
    effectiveConstant
    spinConfig
  simp_rw [pair_energy_identity]
  simp only [Finset.sum_add_distrib]


/-! ## Main theorem -/

/--
The binary-alloy Hamiltonian is exactly an Ising Hamiltonian
with the stated effective coupling, field, and constant.
-/
theorem alloy_eq_ising
    (JAA JBB JAB : Site → Site → ℝ)
    (σ : Config Site) :
    alloyHamiltonian JAA JBB JAB σ
    =
    isingHamiltonian
      (effectiveCoupling JAA JBB JAB)
      (effectiveField JAA JBB)
      (effectiveConstant JAA JBB JAB)
      (spinConfig σ) := by
  rw [alloy_decomposition]
  unfold isingHamiltonian effectiveField
  rw [field_rearrangement]


/-! ## Recovering the formulas in the written solution -/

/--
The effective field in exactly the form written in the solution:

h(r) =
  1/4 Σ_{r'}
    [ J_AA(r,r') - J_BB(r,r')
      + J_AA(r',r) - J_BB(r',r) ].
-/
theorem effectiveField_formula
    (JAA JBB : Site → Site → ℝ)
    (r : Site) :
    effectiveField JAA JBB r
    =
    (1 / 4 : ℝ) *
      ∑ r' : Site,
        ((JAA r r' - JBB r r')
          +
         (JAA r' r - JBB r' r)) := by
  classical
  unfold effectiveField
  rw [
    Finset.sum_add_distrib,
    mul_add,
    Finset.mul_sum,
    Finset.mul_sum
  ]

/--
Likewise,

C =
  1/4 Σ_{r,r'}
      [J_AA(r,r') + J_BB(r,r') + 2 J_AB(r,r')].
-/
theorem effectiveConstant_formula
    (JAA JBB JAB : Site → Site → ℝ) :
    effectiveConstant JAA JBB JAB
    =
    (1 / 4 : ℝ) *
      ∑ r : Site, ∑ r' : Site,
        (JAA r r' + JBB r r' + 2 * JAB r r') := by
  classical
  unfold effectiveConstant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]


/-! ## Zero field and Z₂ symmetry -/

/--
A simple sufficient condition for zero effective field:
J_AA = J_BB pointwise.
-/
theorem effectiveField_zero_of_equal_interactions
    (JAA JBB : Site → Site → ℝ)
    (hEq : ∀ r r', JAA r r' = JBB r r') :
    effectiveField JAA JBB = fun _ => 0 := by
  funext r
  simp [effectiveField, hEq]

/--
An Ising Hamiltonian with h = 0 is invariant under
the global spin flip s ↦ -s.
-/
theorem ising_zeroField_spinFlip
    (J : Site → Site → ℝ)
    (C : ℝ)
    (s : Site → ℝ) :
    isingHamiltonian J (fun _ => 0) C (fun r => -s r)
    =
    isingHamiltonian J (fun _ => 0) C s := by
  classical
  have hpair :
      (∑ r : Site, ∑ r' : Site,
        J r r' * (-s r) * (-s r'))
      =
      ∑ r : Site, ∑ r' : Site,
        J r r' * s r * s r' := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro r' _
    ring
  unfold isingHamiltonian
  simpa only [
    zero_mul,
    Finset.sum_const_zero,
    add_zero
  ] using congrArg (fun x : ℝ => x + C) hpair
end FiniteLattice


/-! ## Optional: recover J(r-r') notation -/

/--
If the lattice itself has an additive-group structure,
a translation-invariant interaction V(r-r') can be turned
into the two-variable kernel used above.
-/
def kernelOfDifference
    {Site : Type*} [AddGroup Site]
    (V : Site → ℝ) :
    Site → Site → ℝ :=
  fun r r' => V (r - r')

end AlloyIsing
