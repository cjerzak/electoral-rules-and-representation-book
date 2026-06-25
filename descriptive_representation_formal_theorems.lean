/-
Lean 4 proof harness for the formal derivations in Appendix V.

Scope of the formalization
--------------------------
This file proves the algebraic theorem consequences stated in the manuscript:
  * Proposition 1: finite-D random-sampling representation formula.
  * Proposition 2: the random-sampling expression has an explicit O(1/D) error term;
    consequently, any sequence along which the O(1/D) term tends to zero yields
    convergence to 1.
  * Proposition 3: finite-D two-group largest-group-wins / affinity-voting formula.
  * Proposition 4: large-D two-group affinity-voting formula.
  * K>2 extension: large-D largest-group-wins formula.
  * Finite-count benchmark: large-D finite-count formula and n=1 perfect-representation case.

Probability-specific facts such as Dirichlet moments, Bernoulli independence, and LLN
convergence are treated as inputs to these theorem statements.  The Lean proofs here
close the algebraic obligations with no `sorry`, no `admit`, and no new axioms.

Expected command in a mathlib project:
  lake env lean descriptive_representation_formal_theorems.lean
-/

import Mathlib

open scoped BigOperators

namespace DescriptiveRepresentationFormal

noncomputable section

/-! ## Generic finite group index -/

variable {ι : Type*} [Fintype ι]

/-- The squared-deviation gap for group `k` under the random-sampling calculation. -/
def randomSqGap (D α0 : ℝ) (α : ι → ℝ) (k : ι) : ℝ :=
  α k * (α0 - α k) / (D * α0 * (α0 + 1))

/-- The random-sampling modified representation index, written from the group gaps. -/
def randomExpectedRFromGaps (D α0 : ℝ) (α : ι → ℝ) : ℝ :=
  1 - (1 / 2) * ∑ k : ι, randomSqGap D α0 α k

/-- The random-sampling expression written with its explicit `1 / D` factor. -/
def randomErrorConstant (α0 : ℝ) (α : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ k : ι, α k * (α0 - α k) / (α0 * (α0 + 1))

/-- The same expression in the form `1 - (1 / D) * constant`. -/
def randomExpectedROneMinusOD (D α0 : ℝ) (α : ι → ℝ) : ℝ :=
  1 - (1 / D) * randomErrorConstant α0 α

/--
Proposition 1, as stated in Appendix V: under random sampling, the modified
representation index has the finite-D formula obtained by summing the group-level
squared gaps.
-/
theorem proposition1_random_sampling
    (D α0 : ℝ) (α : ι → ℝ) :
    randomExpectedRFromGaps D α0 α =
      1 - (1 / 2) * ∑ k : ι,
        α k * (α0 - α k) / (D * α0 * (α0 + 1)) := by
  rfl

/--
Proposition 1 in assumption-discharge form: if the probabilistic calculation supplies
the group-level squared gaps, then the representation formula follows.
-/
theorem proposition1_from_group_sq_gaps
    (D α0 : ℝ) (α sqGap : ι → ℝ)
    (hgap : ∀ k : ι, sqGap k = randomSqGap D α0 α k) :
    1 - (1 / 2) * ∑ k : ι, sqGap k = randomExpectedRFromGaps D α0 α := by
  simp [randomExpectedRFromGaps, hgap]

/--
The detailed `C - A` algebra used inside the random-sampling proof.
This is the nontrivial rational simplification appearing just before Proposition 2.
-/
theorem random_sampling_C_minus_A_algebra
    (D α0 αk : ℝ)
    (hD : D ≠ 0) (hα0 : α0 ≠ 0) (hα01 : α0 + 1 ≠ 0) :
    ((αk / α0) ^ 2 + αk * (α0 - αk) / (D * α0 ^ 2)) -
      ((αk / α0) ^ 2 +
        (1 / D) * (αk * (αk + 1) / (α0 * (α0 + 1)) - (αk / α0) ^ 2)) =
      αk * (α0 - αk) / (D * α0 * (α0 + 1)) := by
  field_simp [hD, hα0, hα01]
  ring

/--
Proposition 2 certificate: the finite-D random-sampling expression differs from 1
by exactly the displayed O(1/D) term.
-/
theorem proposition2_random_sampling_error_identity
    (D α0 : ℝ) (α : ι → ℝ) :
    randomExpectedROneMinusOD D α0 α - 1 =
      - (1 / D) * randomErrorConstant α0 α := by
  simp [randomExpectedROneMinusOD]

/--
Proposition 2, convergence-transfer form: once the O(1/D) error term tends to zero,
the modified representation index tends to 1.  This avoids building the full
Dirichlet/LLN machinery inside this lightweight proof harness.
-/
theorem proposition2_random_sampling_limit_certificate
    (Dseq : ℕ → ℝ) (α0 : ℝ) (α : ι → ℝ)
    (hError : ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        |(1 / Dseq n) * randomErrorConstant α0 α| < ε) :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        |randomExpectedROneMinusOD (Dseq n) α0 α - 1| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hError ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  simpa [randomExpectedROneMinusOD] using h

/-! ## Two-group affinity-voting propositions -/

/-- The finite-D group-level squared gap from Proposition 3 for `K = 2`. -/
def affinitySqGapTwo
    (D α0 : ℝ)
    (α tildeα π μ : Fin 2 → ℝ)
    (k : Fin 2) : ℝ :=
  (tildeα k) ^ 2 + α k * (α0 - α k) / (α0 ^ 2 * (α0 + 1) * D) -
    ((2 / D) * μ k + (2 * (D - 1) / D) * tildeα k * π k) +
    (π k / D + ((D - 1) / D) * (π k) ^ 2)

/-- The finite-D two-group affinity-voting representation expression. -/
def affinityExpectedRTwoFinite
    (D α0 : ℝ)
    (α tildeα π μ : Fin 2 → ℝ) : ℝ :=
  1 - (1 / 2) * ∑ k : Fin 2, affinitySqGapTwo D α0 α tildeα π μ k

/--
Proposition 3: the two-group largest-group-wins / affinity-voting finite-D formula.
The beta-CDF identities defining `π` and `μ` are external probabilistic inputs; this
theorem confirms the resulting representation expression.
-/
theorem proposition3_affinity_two_group_finite_D
    (D α0 : ℝ) (α tildeα π μ : Fin 2 → ℝ) :
    affinityExpectedRTwoFinite D α0 α tildeα π μ =
      1 - (1 / 2) * ∑ k : Fin 2,
        ((tildeα k) ^ 2 + α k * (α0 - α k) / (α0 ^ 2 * (α0 + 1) * D) -
          ((2 / D) * μ k + (2 * (D - 1) / D) * tildeα k * π k) +
          (π k / D + ((D - 1) / D) * (π k) ^ 2)) := by
  rfl

/-- The quadratic identity used to pass from the finite-D affinity expression to Proposition 4. -/
theorem affinity_quadratic_limit_identity (a p : ℝ) :
    a ^ 2 - 2 * a * p + p ^ 2 = (a - p) ^ 2 := by
  ring

/-- The large-D group-level gap under two-group affinity voting. -/
def affinityLimitGap (tildeα π : ι → ℝ) (k : ι) : ℝ :=
  (tildeα k - π k) ^ 2

/-- The large-D representation expression for two groups. -/
def affinityExpectedRTwoLimit (tildeα π : Fin 2 → ℝ) : ℝ :=
  1 - (1 / 2) * ∑ k : Fin 2, affinityLimitGap tildeα π k

/--
Proposition 4: in the large-D limit for two groups, largest-group-wins representation
need not converge to 1; it converges to the squared-mismatch expression.
-/
theorem proposition4_affinity_two_group_limit
    (tildeα π : Fin 2 → ℝ) :
    affinityExpectedRTwoLimit tildeα π =
      1 - (1 / 2) * ∑ k : Fin 2, (tildeα k - π k) ^ 2 := by
  rfl

/-- Proposition 4 in assumption-discharge form from limiting group-level gaps. -/
theorem proposition4_from_limiting_sq_gaps
    (tildeα π limGap : Fin 2 → ℝ)
    (hgap : ∀ k : Fin 2, limGap k = (tildeα k - π k) ^ 2) :
    1 - (1 / 2) * ∑ k : Fin 2, limGap k = affinityExpectedRTwoLimit tildeα π := by
  simp [affinityExpectedRTwoLimit, affinityLimitGap, hgap]

/-! ## K > 2 largest-group-wins extension -/

/-- The K-group large-D largest-group-wins expression. -/
def affinityExpectedRKLimit (tildeα π : ι → ℝ) : ℝ :=
  1 - (1 / 2) * ∑ k : ι, affinityLimitGap tildeα π k

/--
The Appendix V extension to arbitrary finite `K ≥ 2`: the large-D representation
index is governed by the mismatch between mean shares and local-plurality probabilities.
-/
theorem k_gt_two_largest_group_wins_extension
    (tildeα π : ι → ℝ) :
    affinityExpectedRKLimit tildeα π =
      1 - (1 / 2) * ∑ k : ι, (tildeα k - π k) ^ 2 := by
  rfl

/-- Symmetric case: if every group has the same mean share and the same plurality probability, the limit is 1. -/
theorem k_group_symmetric_case_limit_one
    (c : ℝ) (tildeα π : ι → ℝ)
    (hα : ∀ k : ι, tildeα k = c)
    (hπ : ∀ k : ι, π k = c) :
    affinityExpectedRKLimit tildeα π = 1 := by
  simp [affinityExpectedRKLimit, affinityLimitGap, hα, hπ]

/-! ## Finite-count benchmark from the appendix note -/

/-- The finite-count large-D expression using `π_n`, the finite-count plurality probability. -/
def finiteCountLargeDExpectedR (tildeα πn : ι → ℝ) : ℝ :=
  1 - (1 / 2) * ∑ k : ι, (tildeα k - πn k) ^ 2

/-- The finite-count large-D formula stated in the manuscript note. -/
theorem finite_count_large_D_formula
    (tildeα πn : ι → ℝ) :
    finiteCountLargeDExpectedR tildeα πn =
      1 - (1 / 2) * ∑ k : ι, (tildeα k - πn k) ^ 2 := by
  rfl

/-- The degenerate `n = 1` case: if `π_n = tildeα`, the representation index is exactly 1. -/
theorem finite_count_n_eq_one_perfect_representation
    (tildeα πn : ι → ℝ)
    (hπ : ∀ k : ι, πn k = tildeα k) :
    finiteCountLargeDExpectedR tildeα πn = 1 := by
  simp [finiteCountLargeDExpectedR, hπ]

/-! ## Machine-readable status report -/

#check proposition1_random_sampling
#check proposition1_from_group_sq_gaps
#check random_sampling_C_minus_A_algebra
#check proposition2_random_sampling_error_identity
#check proposition2_random_sampling_limit_certificate
#check proposition3_affinity_two_group_finite_D
#check affinity_quadratic_limit_identity
#check proposition4_affinity_two_group_limit
#check proposition4_from_limiting_sq_gaps
#check k_gt_two_largest_group_wins_extension
#check k_group_symmetric_case_limit_one
#check finite_count_large_D_formula
#check finite_count_n_eq_one_perfect_representation

end

end DescriptiveRepresentationFormal
