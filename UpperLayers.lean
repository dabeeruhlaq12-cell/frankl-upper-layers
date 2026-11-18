import Mathlib

/-! Independent targets from the finite proof. No assertion of the full
asymptotic reduction is made in this module. -/
namespace UpperLayers

/-- Two different immediate predecessors of a missing set cannot be present. -/
theorem unique_deletion {α : Type*} [DecidableEq α]
    (F : Finset α → Prop)
    (closed : ∀ s t, F s → F t → F (s ∪ t))
    {s : Finset α} (missing : ¬ F s) {x y : α}
    (hx : F (s.erase x)) (hy : F (s.erase y)) : x = y := by
  classical
  by_contra h
  have hu : s.erase x ∪ s.erase y = s := by
    ext z
    by_cases hzx : z = x
    · subst z
      simp [h]
    · simp [Finset.mem_erase, hzx]
  exact missing (hu ▸ closed _ _ hx hy)

/-- Rank reweighting can only lower the mean when normalized weights
decrease. Cross multiplication also covers zero total weight. -/
theorem weighted_mean_le {ι : Type*} (s : Finset ι)
    (rank w v : ι → ℚ)
    (anti : ∀ i ∈ s, ∀ j ∈ s,
      (rank i - rank j) * (w i * v j - v i * w j) ≤ 0) :
    (∑ i ∈ s, rank i * w i) * (∑ j ∈ s, v j) ≤
      (∑ i ∈ s, rank i * v i) * (∑ j ∈ s, w j) := by
  classical
  have localBound : ∀ i ∈ s, ∀ j ∈ s,
      rank i * w i * v j + rank j * w j * v i ≤
      rank i * v i * w j + rank j * v j * w i := by
    intro i hi j hj
    nlinarith only [anti i hi j hj]
  have summed := Finset.sum_le_sum (s := s) (fun i hi =>
    Finset.sum_le_sum (s := s) (fun j hj => localBound i hi j hj))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at summed
  nlinarith only [summed]

/-- Compute binomial coefficients using exact divisions for kernel reduction. -/
def coeff (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => coeff n k * (n - k) / (k + 1)

theorem coeff_eq_choose (n k : ℕ) : coeff n k = n.choose k := by
  induction k with
  | zero => simp [coeff]
  | succ k ih =>
    rw [coeff, ih, ← Nat.choose_succ_right_eq]
    simp

def prefix (n : ℕ) : ℕ → ℕ
  | 0 => coeff n 0
  | k + 1 => prefix n k + coeff n (k+1)

theorem prefix_eq (n k : ℕ) :
    prefix n k = ∑ j ∈ Finset.range (k+1), n.choose j := by
  induction k with
  | zero => simp [prefix, coeff_eq_choose]
  | succ k ih =>
    change prefix n k + coeff n (k+1) = _
    rw [Finset.sum_range_succ, ih, coeff_eq_choose]

def criterion (n k : ℕ) : Prop :=
  (∑ j ∈ Finset.range (k-2+1), (n-1).choose j) ≤
    (n-1) * (n-2).choose (k-2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem cutoff_59 : criterion 100 59 := by
  unfold criterion
  rw [← prefix_eq, ← coeff_eq_choose]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem cutoff_60 : ¬ criterion 100 60 := by
  unfold criterion
  rw [← prefix_eq, ← coeff_eq_choose]
  decide

#print axioms unique_deletion
#print axioms weighted_mean_le
#print axioms coeff_eq_choose
#print axioms prefix_eq
#print axioms cutoff_59
#print axioms cutoff_60
end UpperLayers
