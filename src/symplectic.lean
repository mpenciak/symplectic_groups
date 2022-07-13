import algebra.lie.classical
import linear_algebra.unitary_group
import data.real.basic
import data.nat.basic
import linear_algebra.matrix.determinant

/-
Unrelated ideas that have come up:
* Maybe refactoring ᵀ into a typeclass
-/

open_locale matrix big_operators

variables {l : Type*}

namespace matrix

section

variables {m n o p q : Type*} {m' n' p' : o → Type*}
variables {R : Type*} {S : Type*} {α : Type*} {β : Type*} [has_neg R] [ring S]

lemma from_blocks_neg_2
  (A : matrix n l R) (B : matrix n m R) (C : matrix o l R) (D : matrix o m R) :
  - (from_blocks A B C D) = from_blocks (-A) (-B) (-C) (-D) :=
begin
  ext i j, cases i; cases j; simp [from_blocks]
end

lemma from_blocks_neg
  (A : matrix n l S) (B : matrix n m S) (C : matrix o l S) (D : matrix o m S) :
  (-1 : S) • (from_blocks A B C D) = - from_blocks (A) (B) (C) (D) :=
begin
  ext i j, cases i; cases j; simp [from_blocks]
end

end

section

open lie_algebra.symplectic

-- TODO: Open more sections to eliminate `l` as an explicit argument in most places

variables (l) [decidable_eq l] [fintype l]  

def symplectic_group : submonoid (matrix (l ⊕ l) (l ⊕ l)  ℝ) := 
{ carrier := { A | A ⬝ (J l ℝ) ⬝ Aᵀ = J l ℝ},
  mul_mem' := 
  begin
    intros a b ha hb,
    --change (a * b) * (J l ℝ) * (a * b)ᵀ = J l ℝ,
    --change (a) * (J l ℝ) * (a)ᵀ = J l ℝ at ha,
    --change (b) * (J l ℝ) * (b)ᵀ = J l ℝ at hb,
    simp only [mul_eq_mul, set.mem_set_of_eq, transpose_mul] at *, 
    rw ←matrix.mul_assoc,
    rw matrix.mul_assoc _ _ (bᵀ),
    rw matrix.mul_assoc a b _,
    rw ←matrix.mul_assoc b _ bᵀ,
    rw hb,
    exact ha,
  end,
  one_mem' := by simp }

namespace symplectic 

lemma mem_symplectic_group_iff {A : matrix (l ⊕ l) (l ⊕ l)  ℝ} :
  A ∈ symplectic_group l ↔ A ⬝ (J l ℝ) ⬝ Aᵀ = J l ℝ :=
by simp [symplectic_group]

instance coe_matrix : has_coe (symplectic_group l) (matrix (l ⊕ l) (l ⊕ l)  ℝ) := ⟨subtype.val⟩

instance coe_fun : has_coe_to_fun (symplectic_group l) (λ _, (l ⊕ l) → (l ⊕ l) → ℝ) :=
{ coe := λ A, A.val }

section coe_lemmas

variables (A B : symplectic_group l)

--@[simp] lemma inv_val : ↑(A⁻¹) = (star A : matrix n n α) := rfl

--@[simp] lemma inv_apply : ⇑(A⁻¹) = (star A : matrix n n α) := rfl

@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma mul_apply : ⇑(A * B) = (A ⬝ B) := rfl

@[simp] lemma one_val : ↑(1 : symplectic_group l) = (1 : matrix (l ⊕ l) (l ⊕ l)  ℝ) := rfl

@[simp] lemma one_apply : ⇑(1 : symplectic_group l) = (1 : matrix (l ⊕ l) (l ⊕ l)  ℝ) := rfl

end coe_lemmas

lemma J_mem : (J l ℝ) ∈ symplectic_group l :=
begin
  rw mem_symplectic_group_iff,
  unfold J,
  rw [from_blocks_multiply, from_blocks_transpose, from_blocks_multiply],
  simp,
end

lemma neg_one_transpose : (-1 : matrix l l ℝ)ᵀ = -1 := by rw [transpose_neg, transpose_one]

lemma J_transpose : - (J l ℝ)ᵀ = (J l ℝ) := 
begin
  unfold J,
  rw [from_blocks_transpose],
  rw ←from_blocks_neg, 
  rw from_blocks_smul,
  rw matrix.transpose_zero,
  rw matrix.transpose_one,
  rw neg_one_transpose,
  simp [from_blocks],
end

-- An old attempt to calculate the determinant by using permutations
-- open sum

-- def bswap (α : Type*) : (α ⊕ α) → (α ⊕ α)
--   | (sum.inl l) := inr l
--   | (sum.inr r) := inl r

-- lemma bswap_bswap {α : Type*} : (bswap α) ∘ (bswap α) = id := 
-- begin
-- ext,
-- cases x;
-- refl
-- end

-- def block_perm : equiv.perm (l ⊕ l) := { to_fun := bswap l,
--   inv_fun := bswap l,
--   left_inv := 
--   begin
--     intro x,
--     change ((bswap l) ∘ (bswap l)) x = x, 
--     rw bswap_bswap,
--     refl,
--   end,
--   right_inv := 
--   begin 
--     intro x,
--     change ((bswap l) ∘ (bswap l)) x = x, 
--     rw bswap_bswap,
--     refl
--   end }


lemma J_squared : (J l ℝ) ⬝ (J l ℝ) = -1 :=
begin
  unfold J,
  rw from_blocks_multiply,
  simp,
  rw ← neg_zero,
  rw ← matrix.from_blocks_neg_2,
  rw ← from_blocks_one,
end

lemma neg_one : (-1 : matrix l l ℝ)  = (-1 : ℝ) • 1  := by simp only [neg_smul, one_smul]

#check neg_one_pow_eq_one_iff_even

lemma minus_powers (n : ℕ) : (-1 : ℝ)^(n + n) = 1 := 
begin
  rw neg_one_pow_eq_one_iff_even,
  exact even_add_self n,
  norm_num,
  /-induction n with n hn,
  simp only [pow_zero],
  calc (-1: ℝ) ^ (n.succ + n.succ) = (-1 : ℝ)^((n + 1) + (n + 1)) : by refl
  ...                              = (-1 : ℝ)^(n + n)*(-1)^2 : by ring_exp
  ...                              = 1 * (-1 : ℝ)^2 : by rw hn
  ...                              = (-1 : ℝ)^2 : by rw one_mul
  ...                              = 1 : by {simp only [neg_one_sq]} -/
end

lemma J_det : det (J l ℝ) = 1 ∨ det (J l ℝ) = - 1:=
begin
  have H : (det (J l ℝ)) * (det (J l ℝ)) = 1 := by {
    rw ← det_mul,
    rw J_squared,
    rw neg_one, 
    rw det_smul, 
    simp,
    rw minus_powers,
  },
  have H2 : (det (J l ℝ))^2 = 1 := by {
    unfold pow,
    unfold monoid.npow,
    unfold ring.npow,
    unfold comm_ring.npow,
    unfold npow_rec,
    rw mul_one,
    exact H,
  } ,
  rw ←sq_eq_one_iff,
  exact H2,
end

lemma pm_one_unit {S : Type*} [ring S] {x : S} (h : x = 1 ∨ x = -1) : is_unit x := 
begin
  cases h,
  {simp [h],},
  { rw h,
    use -1,
    simp,}
end

lemma J_det_unit : is_unit (det (J l ℝ)) := pm_one_unit (J_det l)

lemma neg_mem {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (h : A ∈ symplectic_group l) :
  -A ∈ symplectic_group l :=
begin
  rw mem_symplectic_group_iff at h ⊢,
  simp [h],
end


lemma symplectic_det {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) :
  is_unit $ det A :=
begin
  rw mem_symplectic_group_iff at hA,
  apply_fun det at hA,
  simp at hA,
  have H := J_det l,
  cases H, 
  { rw H at hA,
    simp at hA,
    rw ←sq at hA,
    rw sq_eq_one_iff at hA,
    exact pm_one_unit hA,
  },
  { rw H at hA,
  simp at hA,
  rw ←sq at hA,
  rw sq_eq_one_iff at hA,
  exact pm_one_unit hA,},
end

-- Things have kind of started following apart starting here

noncomputable instance {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) :
  invertible A :=
@matrix.invertible_of_det_invertible (l ⊕ l) ℝ _ _ _ A (is_unit.invertible (symplectic_det l hA))

noncomputable def symplectic_inv {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) :
  symplectic_group l := 
{ val := A⁻¹,
  property := 
  begin
    rw mem_symplectic_group_iff at hA ⊢,
    apply_fun (λ x, A⁻¹ ⬝ (x) ⬝ (Aᵀ)⁻¹) at hA,
    rw matrix.transpose_nonsing_inv,
    calc A⁻¹ ⬝ J l ℝ ⬝ Aᵀ⁻¹ = A⁻¹ ⬝ (A ⬝ J l ℝ ⬝ Aᵀ) ⬝ Aᵀ⁻¹ : by exact hA.symm
    -- These should be easy but I'm stuck on them as well (`change` worked befoe)
    ...                     = A⁻¹ * A * J l ℝ * Aᵀ * Aᵀ⁻¹ : by sorry 
    ...                     = (A⁻¹ * A) * (J l ℝ) * (Aᵀ * Aᵀ⁻¹) : by simp only [mul_assoc]
    ...                     = 1 * (J l ℝ) * 1 : by sorry -- should be `inv_of_mul_self` & `mul_inv_of_self` or something?
    ...                     = J l ℝ : by simp
  end }


-- I think at this point I'm starting to realize I shouldn't be using `A ∈ symplectic l`...
noncomputable instance : group (symplectic_group l) := {
  inv := λ A, symplectic_inv l A.2, 
  mul_left_inv := 
  begin
  intro A,
  unfold has_inv.inv,
  unfold div_inv_monoid.inv,
  unfold symplectic_inv,
  simp,
  -- Not sure how to deal with this `⟨(↑A)⁻¹, _⟩ * A = 1`
  sorry
  end,
  .. submonoid.to_monoid _ }
  
end symplectic

end

end matrix

-- TODO: Add this back in 
-- def symplectic_transpose : symplectic l → symplectic l := fun A, 
-- { val := Aᵀ,
--   property :=
--   begin 
--    sorry
--   end }