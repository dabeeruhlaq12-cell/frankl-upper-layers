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
        simp [good, bad]
        tauto
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
    (fun (s : Finset (Fin n)) (x : Fin n) => x ∈ s) (s := F) (t := Finset.univ)
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

/-- Increasing the rank decreases the fraction of the pointed-cube rank
occupied by missing sets. The ground size here is n+1. -/
theorem ratio_bound {n : ℕ} (F : Finset (Finset (Fin (n+1))))
    (closed : ∀ s t, s ∈ F → t ∈ F → s ∪ t ∈ F) :
    ∀ i j : ℕ, i ≤ j → j ≤ n →
    ((missingLevel F (j+1)).card : ℚ) / n.choose j ≤
      ((missingLevel F (i+1)).card : ℚ) / n.choose i := by
  let d := fun i => ((missingLevel F (i+1)).card : ℚ)
  let b := fun i => (n.choose i : ℚ)
  have pos {i} (hi : i ≤ n) : 0 < b i := by
    dsimp [b]; exact_mod_cast Nat.choose_pos hi
  have step (i : ℕ) (hi : i+1 ≤ n) : d (i+1) / b (i+1) ≤ d i / b i := by
    have raw := missing_rank_bound F closed (r := i+1)
    have raw' : d (i+1) * (i+1 : ℕ) ≤ d i * (n-i : ℕ) := by
      dsimp [d]
      exact_mod_cast (show (missingLevel F (i+1+1)).card * (i+1) ≤
          (missingLevel F (i+1)).card * (n-i) by simpa using raw)
    have eq : b (i+1) * (i+1 : ℕ) = b i * (n-i : ℕ) := by
      dsimp [b]; exact_mod_cast Nat.choose_succ_right_eq n i
    apply (div_le_div_iff₀ (pos hi) (pos (by omega))).2
    have h := mul_le_mul_of_nonneg_right raw' (pos (by omega : i ≤ n)).le
    have e := congrArg (fun t : ℚ => d i * t) eq
    have hi' : 0 < ((i+1 : ℕ) : ℚ) := by positivity
    by_contra! hlt
    change d i * (b (i+1) * _) = d i * (b i * _) at e
    have bad := mul_pos (sub_pos.mpr hlt) hi'
    linarith only [h, e, bad]
  intro i j
  induction j with
  | zero =>
    intro h _
    have hi : i = 0 := by omega
    rw [hi]
  | succ j ih =>
    intro hij hj
    by_cases he : i = j+1
    · subst i; rfl
    · exact (step j hj).trans (ih (by omega) (by omega))

/-- Signed pointed-binomial test. The paper shows that this test is
equivalent to its binomial-prefix criterion. k is the number of
positive missing ranks allowed, so the upper layer starts at k+1. -/
def signedTest (n k : ℕ) : Prop :=
  (∑ i ∈ Finset.range k, (2*((i : ℚ)+1)-(n+1 : ℕ)) * n.choose i) ≤ 0

theorem upper_layer_mass {n k : ℕ} (hk : k ≤ n+1)
    (F : Finset (Finset (Fin (n+1))))
    (closed : ∀ s t, s ∈ F → t ∈ F → s ∪ t ∈ F)
    (upper : ∀ s : Finset (Fin (n+1)), k+1 ≤ s.card → s ∈ F)
    (test : signedTest n k) :
    0 ≤ mass F := by
  classical
  let w := fun i : ℕ => 2*((i : ℚ)+1)-(n+1 : ℕ)
  let d := fun i : ℕ => ((missingLevel F (i+1)).card : ℚ)
  let b := fun i : ℕ => (n.choose i : ℚ)
  let p := n/2
  have hp : p ≤ n := by dsimp [p]; omega
  let ρ := d p / b p
  have hr : 0 ≤ ρ := by dsimp [ρ,d,b]; positivity
  have bound (i : ℕ) (hi : i < k) : w i * d i ≤ ρ * (w i * b i) := by
    have hin : i ≤ n := by omega
    have hb : 0 < b i := by dsimp [b]; exact_mod_cast Nat.choose_pos hin
    by_cases he : i = p
    · subst i
      apply le_of_eq
      calc
        w p * d p = w p * (d p / b p * b p) := by rw [div_mul_cancel₀ _ hb.ne']
        _ = _ := by dsimp [ρ]; ring
    · by_cases hlo : i < p
      · have h : ρ ≤ d i / b i := ratio_bound F closed i p hlo.le hp
        have hsign : w i ≤ 0 := by
          dsimp [w,p] at *
          exact_mod_cast (show (2*(i+1) : ℤ) - (n+1 : ℕ) ≤ 0 by omega)
        have hh := mul_le_mul_of_nonpos_left ((le_div_iff₀ hb).1 h) hsign
        linarith only [hh]
      · have h : d i / b i ≤ ρ := ratio_bound F closed p i (by omega) hin
        have hsign : 0 ≤ w i := by
          dsimp [w,p] at *
          exact_mod_cast (show (0 : ℤ) ≤ 2*(i+1) - (n+1 : ℕ) by omega)
        have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hb).1 h) hsign
        linarith only [hh]
  have hs : (∑ i ∈ Finset.range k, w i * d i) ≤ 0 := by
    have h := Finset.sum_le_sum (s := Finset.range k)
      (fun i hi => bound i (Finset.mem_range.mp hi))
    rw [← Finset.mul_sum] at h
    exact h.trans (mul_nonpos_of_nonneg_of_nonpos hr test)
  have trunc : (∑ i ∈ Finset.range k, w i * d i) =
      ∑ i ∈ Finset.range (n+1), w i * d i := by
    apply Finset.sum_subset (Finset.range_mono hk)
    intro i _ hi
    have hk' : k ≤ i := by simpa using hi
    have empty : missingLevel F (i+1) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro s h
      have hh : s.card = i+1 ∧ s ∉ F := (Finset.mem_filter.mp h).2
      exact hh.2 (upper s (by omega))
    simp [d, empty]
  rw [trunc] at hs
  have hmissing : mass (Finset.univ \ F) ≤ 0 := by
    rw [mass_missing, Finset.sum_range_succ']
    change (∑ i ∈ Finset.range (n+1), (2*((i+1 : ℕ) : ℚ)-(n+1 : ℕ)) * d i) +
        (2*(0:ℚ)-(n+1 : ℕ)) * ((missingLevel F 0).card : ℚ) ≤ 0
    push_cast
    dsimp [w] at hs
    push_cast at hs
    have hz : 0 ≤ ((missingLevel F 0).card : ℚ) := by positivity
    nlinarith
  have hcube := mass_univ (n+1)
  have hsplit : mass (Finset.univ \ F) + mass F =
      mass (Finset.univ : Finset (Finset (Fin (n+1)))) := by
    unfold mass
    exact Finset.sum_sdiff (Finset.subset_univ F)
  linarith

theorem upper_layer_abundance {n k : ℕ} (hk : k ≤ n+1)
    (F : Finset (Finset (Fin (n+1))))
    (closed : ∀ s t, s ∈ F → t ∈ F → s ∪ t ∈ F)
    (upper : ∀ s : Finset (Fin (n+1)), k+1 ≤ s.card → s ∈ F)
    (test : signedTest n k) :
    ∃ x : Fin (n+1), F.card ≤ 2 * (F.filter (fun s => x ∈ s)).card := by
  exact abundant_of_mass (by omega) F (upper_layer_mass hk F closed upper test)

#print axioms upper_layer_abundance

/-- Telescope the signed binomial mass. The upper limit k is exclusive. -/
theorem signed_identity (n k : ℕ) (hk : k ≤ n+1) :
    (∑ i ∈ Finset.range k, (2*((i : ℚ)+1)-(n+1 : ℕ)) * n.choose i) =
    (∑ i ∈ Finset.range k, (n.choose i : ℚ)) - (k : ℚ) * n.choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k ≤ n := by omega
    have h : (n.choose (k+1) : ℚ) * (k+1 : ℕ) =
        (n.choose k : ℚ) * (n-k : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq n k
    push_cast [Nat.cast_sub hkn] at h
    rw [Finset.sum_range_succ, ih (by omega), Finset.sum_range_succ]
    push_cast
    linarith only [h]

theorem signed_iff_criterion (m r : ℕ) (hr : r ≤ m) :
    signedTest (m+1) (r+1) ↔ criterion (m+2) (r+2) := by
  unfold signedTest
  rw [signed_identity _ _ (by omega), sub_nonpos]
  unfold criterion
  have h := Nat.succ_mul_choose_eq m r
  change (m+1) * m.choose r = (m+1).choose (r+1) * (r+1) at h
  change (_ ≤ _) ↔ (∑ i ∈ Finset.range (r+1), (m+1).choose i) ≤ (m+1)*m.choose r
  rw [h, Nat.mul_comm ((m+1).choose (r+1)) (r+1)]
  norm_cast

/-- The binomial criterion in the research note implies abundance for all
union-closed families on a ground of size m+2 with cutoff r+2. -/
theorem finite_criterion {m r : ℕ} (hr : r ≤ m)
    (F : Finset (Finset (Fin (m+2))))
    (closed : ∀ s t, s ∈ F → t ∈ F → s ∪ t ∈ F)
    (upper : ∀ s : Finset (Fin (m+2)), r+2 ≤ s.card → s ∈ F)
    (h : criterion (m+2) (r+2)) :
    ∃ x : Fin (m+2), F.card ≤ 2 * (F.filter (fun s => x ∈ s)).card :=
  upper_layer_abundance (n := m+1) (k := r+1) (by omega) F closed upper
    ((signed_iff_criterion m r hr).2 h)

#print axioms finite_criterion

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
theorem hundred_element_cutoff
    (F : Finset (Finset (Fin 100)))
    (closed : ∀ s t, s ∈ F → t ∈ F → s ∪ t ∈ F)
    (upper : ∀ s : Finset (Fin 100), 59 ≤ s.card → s ∈ F) :
    ∃ x : Fin 100, F.card ≤ 2 * (F.filter (fun s => x ∈ s)).card := by
  exact finite_criterion (m := 98) (r := 57) (by decide) F closed upper cutoff_59

#print axioms hundred_element_cutoff

/-- Complement of the truncated star of missing sets. -/
def starFamily {n : ℕ} (x : Fin (n+1)) (k : ℕ) :=
  Finset.univ.filter (fun s : Finset (Fin (n+1)) => x ∉ s ∨ k+1 ≤ s.card)

theorem star_upper {n : ℕ} (x : Fin (n+1)) (k : ℕ)
    (s : Finset (Fin (n+1))) (h : k+1 ≤ s.card) : s ∈ starFamily x k := by
  simp [starFamily, h]

theorem star_closed {n : ℕ} (x : Fin (n+1)) (k : ℕ)
    (s t : Finset (Fin (n+1))) (hs : s ∈ starFamily x k) (ht : t ∈ starFamily x k) :
    s ∪ t ∈ starFamily x k := by
  have hs' := (Finset.mem_filter.mp hs).2
  have ht' := (Finset.mem_filter.mp ht).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases hs' with h | h
  · rcases ht' with g | g
    · left; simpa using And.intro h g
    · right; exact g.trans (Finset.card_le_card Finset.subset_union_right)
  · right; exact h.trans (Finset.card_le_card Finset.subset_union_left)

theorem star_zero {n : ℕ} (x : Fin (n+1)) (k : ℕ) :
    missingLevel (starFamily x k) 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro s hs
  have h : s.card = 0 ∧ s ∉ starFamily x k := (Finset.mem_filter.mp hs).2
  have he := Finset.card_eq_zero.mp h.1
  exact h.2 (by simp [he, starFamily])

theorem star_ranks {n k i : ℕ} (x : Fin (n+1)) :
    (missingLevel (starFamily x k) (i+1)).card = if i < k then n.choose i else 0 := by
  classical
  split_ifs with hi
  · let u := (Finset.univ : Finset (Fin (n+1))).erase x
    let level := u.powersetCard i
    have hx {s : Finset (Fin (n+1))} (hs : s ∈ level) : x ∉ s := by
      intro h
      have hsub := (Finset.mem_powersetCard.mp hs).1
      have := hsub h
      simp [u] at this
    have heq : missingLevel (starFamily x k) (i+1) =
        level.image (fun s => insert x s) := by
      ext s
      constructor
      · intro h
        have hp : s.card = i+1 ∧ s ∉ starFamily x k := (Finset.mem_filter.mp h).2
        have hxs : x ∈ s := by
          by_contra hnot
          exact hp.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hnot⟩)
        apply Finset.mem_image.mpr
        refine ⟨s.erase x, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.insert_erase hxs⟩
        · intro y hy; exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, Finset.mem_univ _⟩
        · simp [Finset.card_erase_of_mem hxs, hp.1]
      · intro h
        obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
        have hcard := (Finset.mem_powersetCard.mp ht).2
        have hs : (insert x t).card = i+1 := by rw [Finset.card_insert_of_not_mem (hx ht), hcard]
        simp [missingLevel, starFamily, hs, hi, show ¬k+1 ≤ i+1 by omega]
    rw [heq, Finset.card_image_of_injOn]
    · dsimp [level]
      rw [Finset.card_powersetCard]
      simp [u, Finset.card_erase_of_mem]
    · intro s hs t ht he
      change insert x s = insert x t at he
      have he' := congrArg (fun a : Finset (Fin (n+1)) => a.erase x) he
      simpa [Finset.erase_insert (hx hs), Finset.erase_insert (hx ht)] using he'
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro s hs
    have hp : s.card = i+1 ∧ s ∉ starFamily x k := (Finset.mem_filter.mp hs).2
    exact hp.2 (star_upper x k s (by omega))

theorem star_mass {n k : ℕ} (hk : k ≤ n+1) (x : Fin (n+1)) :
    mass (starFamily x k) =
      -(∑ i ∈ Finset.range k, (2*((i : ℚ)+1)-(n+1 : ℕ)) * n.choose i) := by
  classical
  let F := starFamily x k
  have split : mass (Finset.univ \ F) + mass F = 0 := by
    rw [← mass_univ (n+1)]
    exact Finset.sum_sdiff (Finset.subset_univ F)
  rw [mass_missing, Finset.sum_range_succ'] at split
  dsimp [F] at split
  simp only [star_zero, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero,
    star_ranks, Nat.cast_ite, Nat.cast_add, Nat.cast_one] at split
  have ht : (Finset.range (n+1)).filter (fun i => i < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp_rw [mul_ite, mul_zero] at split
  rw [← Finset.sum_filter, ht] at split
  push_cast
  linarith

/-- Sharp finite characterization of the averaging property. -/
theorem exact_averaging_criterion (m r : ℕ) (hr : r ≤ m) :
    criterion (m+2) (r+2) ↔
    ∀ F : Finset (Finset (Fin (m+2))),
      (∀ s t, s ∈ F → t ∈ F → s ∪ t ∈ F) →
      (∀ s : Finset (Fin (m+2)), r+2 ≤ s.card → s ∈ F) → 0 ≤ mass F := by
  constructor
  · intro hc F closed upper
    exact upper_layer_mass (n := m+1) (k := r+1) (by omega) F closed upper
      ((signed_iff_criterion m r hr).2 hc)
  · intro h
    let x : Fin (m+2) := ⟨0, by omega⟩
    have hstar := h (starFamily x (r+1)) (star_closed x (r+1)) (star_upper x (r+1))
    rw [star_mass (n := m+1) (by omega)] at hstar
    apply (signed_iff_criterion m r hr).1
    unfold signedTest
    linarith

#print axioms exact_averaging_criterion

end UpperLayers
