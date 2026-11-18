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

/-- Missing sets of a specified size on a finite ground. -/
def missingLevel {n : ℕ} (F : Finset (Finset (Fin n))) (r : ℕ) :=
  Finset.univ.filter (fun s : Finset (Fin n) => s.card = r ∧ s ∉ F)

/-- The adjacent-rank inequality, for arbitrary dimension and family. -/
theorem missing_rank_bound {n r : ℕ} (F : Finset (Finset (Fin n)))
    (closed : ∀ s t, s ∈ F → t ∈ F → s ∪ t ∈ F) :
    (missingLevel F (r+1)).card * r ≤ (missingLevel F r).card * (n-r) := by
  classical
  let edge := fun (a b : Finset (Fin n)) => ∃ x ∈ a, a.erase x = b
  apply Finset.card_mul_le_card_mul edge
  · intro a ha
    have hp : a.card = r+1 ∧ a ∉ F := (Finset.mem_filter.mp ha).2
    obtain ⟨hsize, habsent⟩ := hp
    let good := a.filter (fun x => a.erase x ∉ F)
    let bad := a.filter (fun x => a.erase x ∈ F)
    have hbad : bad.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      exact unique_deletion (fun s => s ∈ F) closed habsent
        (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    have partition : good.card + bad.card = a.card := by
      have hu : good ∪ bad = a := by
        ext x
        simp [good, bad] <;> tauto
      have hd : Disjoint good bad := Finset.disjoint_left.mpr (by
        intro x hx hy
        exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2)
      rw [← Finset.card_union_of_disjoint hd, hu]
    have enough : r ≤ good.card := by omega
    apply enough.trans
    apply Finset.card_le_card_of_injOn (fun x => a.erase x)
    · intro x hx
      obtain ⟨hxa, hm⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨?_, x, hxa, rfl⟩
      simp [missingLevel, Finset.card_erase_of_mem hxa, hsize, hm]
    · intro x hx y hy he
      by_contra hxy
      have hin : x ∈ a.erase y :=
        Finset.mem_erase.mpr ⟨hxy,(Finset.mem_filter.mp hx).1⟩
      change a.erase x = a.erase y at he
      rw [← he] at hin
      simp at hin
  · intro b hb
    have hsize : b.card = r := (Finset.mem_filter.mp hb).2.1
    let outside : Finset (Fin n) := Finset.univ \ b
    have sub : Finset.bipartiteBelow edge (missingLevel F (r+1)) b ⊆
        outside.image (fun x => insert x b) := by
      intro a ha
      obtain ⟨x,hxa,hxb⟩ := (Finset.mem_filter.mp ha).2
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, ?_⟩
      · simp [outside, ← hxb]
      · rw [← hxb, Finset.insert_erase hxa]
    calc
      _ ≤ _ := Finset.card_le_card sub
      _ ≤ outside.card := Finset.card_image_le
      _ = _ := by
        change bᶜ.card = n-r
        simp [Finset.card_compl, hsize]

#print axioms missing_rank_bound

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

def binomPrefix (n : ℕ) : ℕ → ℕ
  | 0 => coeff n 0
  | k + 1 => binomPrefix n k + coeff n (k+1)

theorem binomPrefix_eq (n k : ℕ) :
    binomPrefix n k = ∑ j ∈ Finset.range (k+1), n.choose j := by
  induction k with
  | zero => simp [binomPrefix, coeff_eq_choose]
  | succ k ih =>
    change binomPrefix n k + coeff n (k+1) = _
    rw [Finset.sum_range_succ, ih, coeff_eq_choose]

def criterion (n k : ℕ) : Prop :=
  (∑ j ∈ Finset.range (k-2+1), (n-1).choose j) ≤
    (n-1) * (n-2).choose (k-2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem cutoff_59 : criterion 100 59 := by
  unfold criterion
  rw [← binomPrefix_eq, ← coeff_eq_choose]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem cutoff_60 : ¬ criterion 100 60 := by
  unfold criterion
  rw [← binomPrefix_eq, ← coeff_eq_choose]
  decide

#print axioms unique_deletion
#print axioms weighted_mean_le
#print axioms coeff_eq_choose
#print axioms binomPrefix_eq
#print axioms cutoff_59
#print axioms cutoff_60

/-- Total excess of element occurrences, multiplied by two. -/
def mass {n : ℕ} (F : Finset (Finset (Fin n))) : ℚ :=
  ∑ s ∈ F, (2 * (s.card : ℚ) - n)

/-- Nonnegative total mass witnesses an abundant coordinate. -/
theorem abundant_of_mass {n : ℕ} (hn : 0 < n)
    (F : Finset (Finset (Fin n))) (hm : 0 ≤ mass F) :
    ∃ x : Fin n, F.card ≤ 2 * (F.filter (fun s => x ∈ s)).card := by
  classical
  by_contra! no
  have hdeg (s : Finset (Fin n)) :
      (Finset.univ.filter (fun x => x ∈ s)) = s := by ext x; simp
  have count := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (s : Finset (Fin n)) (x : Fin n) => x ∈ s) F Finset.univ
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, hdeg] at count
  have all : (∑ x : Fin n, 2 * (F.filter (fun s => x ∈ s)).card) <
      ∑ _x : Fin n, F.card := by
    exact Finset.sum_lt_sum (fun x _ => (no x).le)
      ⟨⟨0,hn⟩, Finset.mem_univ _, no _⟩
  rw [← Finset.mul_sum, ← count] at all
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at all
  unfold mass at hm
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hm
  have hrat : 2 * (∑ s ∈ F, (s.card : ℚ)) < (n : ℚ) * F.card := by
    exact_mod_cast all
  nlinarith

/-- The full cube has mean rank exactly n/2 by complement symmetry. -/
theorem mass_univ (n : ℕ) : mass (Finset.univ : Finset (Finset (Fin n))) = 0 := by
  classical
  let e : Finset (Fin n) ≃ Finset (Fin n) :=
    ⟨fun s => sᶜ, fun s => sᶜ, compl_compl, compl_compl⟩
  let g := fun s : Finset (Fin n) => 2 * (s.card : ℚ) - n
  have neg (s : Finset (Fin n)) : g (e s) = -g s := by
    change 2 * ((sᶜ.card : ℕ) : ℚ) - n = -(2 * (s.card : ℚ) - n)
    have hn : s.card ≤ n := by simpa using s.card_le_univ
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub hn]
    ring
  have h := e.sum_comp g
  simp only [neg, Finset.sum_neg_distrib] at h
  change (∑ x, g x) = 0
  linarith

/-- Bookkeeping for the missing ranks on a finite ground. -/
theorem mass_missing {n : ℕ} (F : Finset (Finset (Fin n))) :
    mass (Finset.univ \ F) =
    ∑ i ∈ Finset.range (n+1), (2*(i : ℚ)-n) * (missingLevel F i).card := by
  classical
  let D := Finset.univ \ F
  let w := fun i : ℕ => 2*(i : ℚ)-n
  change (∑ s ∈ D, w s.card) = _
  calc
    _ = ∑ s ∈ D, ∑ i ∈ Finset.range (n+1), if i = s.card then w i else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      have hs : s.card ≤ n := by simpa using s.card_le_univ
      simp [Finset.mem_range, Nat.lt_succ_of_le hs]
    _ = ∑ i ∈ Finset.range (n+1), ∑ s ∈ D, if i = s.card then w i else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have eq : D.filter (fun s => i = s.card) = missingLevel F i := by
        ext s
        simp [D, missingLevel, eq_comm, and_comm]
      rw [← Finset.sum_filter, Finset.sum_const, eq, nsmul_eq_mul]
      simp [w, mul_comm]

#print axioms abundant_of_mass
#print axioms mass_univ
#print axioms mass_missing

end UpperLayers
