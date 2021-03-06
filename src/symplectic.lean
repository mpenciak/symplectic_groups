import algebra.lie.classical
import linear_algebra.unitary_group
import data.real.basic
import data.nat.basic
import linear_algebra.matrix.determinant
import linear_algebra.matrix.nonsingular_inverse

/-
Unrelated ideas that have come up:
* Maybe refactoring ᵀ into a typeclass
-/

open_locale matrix big_operators

variables {l : Type*}

namespace matrix

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

end matrix

section

open lie_algebra.symplectic matrix

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
    rw a.mul_assoc,
    rw a.mul_assoc,
    rw hb,
    exact ha,
  end,
  one_mem' := by simp }

variables {l} -- MD: I am making the l implicit whenever we know l from the context already

namespace symplectic_group

lemma mem_symplectic_group_iff {A : matrix (l ⊕ l) (l ⊕ l)  ℝ} :
  A ∈ symplectic_group l ↔ A ⬝ (J l ℝ) ⬝ Aᵀ = J l ℝ :=
by simp [symplectic_group]

instance coe_matrix : has_coe (symplectic_group l) (matrix (l ⊕ l) (l ⊕ l)  ℝ) := ⟨subtype.val⟩

instance coe_fun : has_coe_to_fun (symplectic_group l) (λ _, (l ⊕ l) → (l ⊕ l) → ℝ) :=
{ coe := λ A, A.val }

section coe_lemmas

variables (A B : symplectic_group l)

@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma mul_apply : ⇑(A * B) = (A ⬝ B) := rfl

@[simp] lemma one_val : ↑(1 : symplectic_group l) = (1 : matrix (l ⊕ l) (l ⊕ l)  ℝ) := rfl

@[simp] lemma one_apply : ⇑(1 : symplectic_group l) = (1 : matrix (l ⊕ l) (l ⊕ l)  ℝ) := rfl

lemma mul_mem {A B : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) (hB : B ∈ symplectic_group l) : 
A ⬝ B ∈ symplectic_group l :=
submonoid.mul_mem _ hA hB

end coe_lemmas

variables (l)

lemma J_mem : (J l ℝ) ∈ symplectic_group l :=
begin
  rw mem_symplectic_group_iff,
  unfold J,
  rw [from_blocks_multiply, from_blocks_transpose, from_blocks_multiply],
  simp,
end

def sym_J : symplectic_group l := ⟨J l ℝ, J_mem l⟩

variables {l}

@[simp] lemma coe_J : ↑(sym_J l) = J l ℝ := rfl

@[simp] lemma J_apply : ⇑(sym_J l) = J l ℝ := rfl

lemma neg_one_transpose : (-1 : matrix l l ℝ)ᵀ = -1 := by rw [transpose_neg, transpose_one]

@[simp] lemma J_transpose : (J l ℝ)ᵀ = - (J l ℝ) := 
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

lemma J_inv : (J l ℝ)⁻¹ = -(J l ℝ) :=
begin
  refine matrix.inv_eq_right_inv _,
  rw [matrix.mul_neg, J_squared],
  exact neg_neg 1,
end


lemma neg_one : (-1 : matrix l l ℝ)  = (-1 : ℝ) • 1  := by simp only [neg_smul, one_smul]

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

variables (l)

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

variables {l}

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

instance : has_neg (symplectic_group l) :=
{ neg := λ A, ⟨-A, neg_mem A.2⟩}

@[simp] lemma coe_neg (A : symplectic_group l): (↑(-A) : matrix _ _ _) = -A := rfl

@[simp] lemma neg_apply (A : symplectic_group l): ⇑(-A) = -A := rfl

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

lemma transpose_mem {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) : Aᵀ ∈ symplectic_group l :=
begin
  rw mem_symplectic_group_iff at ⊢ hA,
  rw transpose_transpose,
  have huA := symplectic_det hA,
  have huAT : is_unit (Aᵀ).det :=
  begin
    rw matrix.det_transpose,
    exact huA,
  end,

  calc Aᵀ ⬝ J l ℝ ⬝ A = - Aᵀ ⬝ (J l ℝ)⁻¹ ⬝ A  : by {rw J_inv, simp}
  -- ...                 = - Aᵀ ⬝ (J l ℝ)⁻¹ ⬝ A  : by 
  ...                 = - Aᵀ ⬝ (A ⬝ J l ℝ ⬝ Aᵀ)⁻¹ ⬝ A : by rw hA
  ...                 = - (Aᵀ ⬝ (Aᵀ⁻¹ ⬝ (J l ℝ)⁻¹)) ⬝ A⁻¹ ⬝ A : by simp [matrix.mul_inv_rev, matrix.mul_assoc]
  ...                 = - (J l ℝ)⁻¹ : by rw [matrix.mul_nonsing_inv_cancel_left _ _ huAT, nonsing_inv_mul_cancel_right _ _ huA]
  ...                 = (J l ℝ) : by simp [J_inv]
end

lemma transpose_mem_iff {A : matrix (l ⊕ l) (l ⊕ l) ℝ} : Aᵀ ∈ symplectic_group l ↔ A ∈ symplectic_group l :=
⟨λ hA, by simpa using transpose_mem hA , transpose_mem⟩

lemma mem_symplectic_group_iff' {A : matrix (l ⊕ l) (l ⊕ l)  ℝ} :
  A ∈ symplectic_group l ↔ Aᵀ ⬝ (J l ℝ) ⬝ A = J l ℝ := 
by rw [←transpose_mem_iff, mem_symplectic_group_iff,transpose_transpose]

-- Things have kind of started following apart starting here

noncomputable def symplectic_inv {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) :
  symplectic_group l :=
{ val := A⁻¹,
  property :=
  begin
    have huA := symplectic_det hA,
    have huAT : is_unit (Aᵀ).det :=
    begin
      rw matrix.det_transpose,
      exact huA,
    end,
    rw mem_symplectic_group_iff at hA ⊢,
    apply_fun (λ x, A⁻¹ ⬝ (x) ⬝ (Aᵀ)⁻¹) at hA,
    rw matrix.transpose_nonsing_inv,
    calc A⁻¹ ⬝ J l ℝ ⬝ Aᵀ⁻¹ = A⁻¹ ⬝ (A ⬝ J l ℝ ⬝ Aᵀ) ⬝ Aᵀ⁻¹ : by rw hA
    ...                     = A⁻¹ ⬝ A ⬝ J l ℝ ⬝ Aᵀ ⬝ Aᵀ⁻¹ : by simp only [matrix.mul_assoc]
    ...                     = (A⁻¹ ⬝ A) ⬝ (J l ℝ) ⬝ (Aᵀ ⬝ Aᵀ⁻¹) : by simp only [matrix.mul_assoc]
    ...                     = 1 ⬝ (J l ℝ) ⬝ (Aᵀ ⬝ Aᵀ⁻¹) : by rw A.nonsing_inv_mul huA
    ...                     = 1 ⬝ (J l ℝ) ⬝ 1 : by rw Aᵀ.mul_nonsing_inv huAT
    ...                     = J l ℝ : by simp
  end }

def computable_symp_inv {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) :
  A ⬝ (- (J l ℝ) ⬝ Aᵀ ⬝ (J l ℝ)) = 1 :=
  begin
  rw mem_symplectic_group_iff at hA,
  calc A ⬝ (-J l ℝ ⬝ Aᵀ ⬝ J l ℝ) = - (A ⬝ (J l ℝ) ⬝ Aᵀ) ⬝ (J l ℝ) : by simp [matrix.mul_assoc]
  ...                            = - (J l ℝ) ⬝ (J l ℝ) : by rw hA
  ...                            = (-1 : ℝ) • ( (J l ℝ) ⬝ (J l ℝ) ) : by simp
  ...                            = - (-1) : by {rw J_squared, simp}
  ...                            = 1 : by simp,
  end

-- def computable_symp_inv {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) : 
--   symplectic_group l :=
-- { val := - (J l ℝ) ⬝ Aᵀ ⬝ (J l ℝ),
--   property := 
--   begin
--     rw mem_symplectic_group_iff at hA ⊢,
--     simp
--     sorry
--   end }

lemma inv_mem_aux {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) :
  - (J l ℝ) ⬝ Aᵀ ⬝ (J l ℝ) ∈ symplectic_group l :=
mul_mem (mul_mem (neg_mem $ J_mem _) $ transpose_mem hA) $ J_mem _ 
  -- simp only [matrix.neg_mul, transpose_neg, transpose_mul, J_transpose, transpose_transpose, matrix.mul_neg, neg_neg],
  -- rw matrix.mul_assoc _ _ (J l ℝ),
  -- rw J_squared,
  -- rw matrix.transpose_mul,
  -- rw matrix.transpose_mul,
  -- rw matrix.transpose_transpose,
  -- rw matrix.transpose_neg,

lemma inv_left_mul_aux {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) :
  -(J l ℝ ⬝ Aᵀ ⬝ J l ℝ ⬝ A) = 1 :=
calc -(J l ℝ ⬝ Aᵀ ⬝ J l ℝ ⬝ A) = - J l ℝ ⬝ (Aᵀ ⬝ J l ℝ ⬝ A) : by simp [matrix.mul_assoc]
...                            = - J l ℝ ⬝ J l ℝ : by {rw mem_symplectic_group_iff' at hA, rw hA}
...                            = (-1 : ℝ) • (J l ℝ ⬝ J l ℝ) : by simp only [matrix.neg_mul, neg_smul, one_smul]
...                            = (-1 : ℝ) • -1 : by rw J_squared
...                            = 1 : by simp only [neg_smul_neg, one_smul]

instance : has_inv (symplectic_group l) := {
  inv := λ A, ⟨- (J l ℝ) ⬝ Aᵀ ⬝ (J l ℝ),
    mul_mem (mul_mem (neg_mem $ J_mem _) $ transpose_mem A.2) $ J_mem _⟩,
}

@[simp] lemma coe_inv (A : symplectic_group l): (↑(A⁻¹) : matrix _ _ _) = - (J l ℝ) ⬝ Aᵀ ⬝ (J l ℝ) := rfl

@[simp] lemma inv_apply (A : symplectic_group l): ⇑(A⁻¹) = - (J l ℝ) ⬝ Aᵀ ⬝ (J l ℝ) := rfl

instance : group (symplectic_group l) := {
  mul_left_inv :=
  begin
    intro A,
    apply subtype.ext,
    simp,
    exact inv_left_mul_aux A.2,
  end,
  .. symplectic_group.has_inv,
  .. submonoid.to_monoid _
}

-- I think at this point I'm starting to realize I shouldn't be using `A ∈ symplectic l`...
noncomputable instance old : group (symplectic_group l) := {
  inv := λ A, symplectic_inv A.2, 
  mul_left_inv := 
  begin
  intro A,
  apply subtype.ext,
  simp,
  -- rw matrix.nonsing_inv_mul,
  -- unfold has_inv.inv,
  -- unfold div_inv_monoid.inv,
  -- unfold symplectic_inv,

  -- Not sure how to deal with this `⟨(↑A)⁻¹, _⟩ * A = 1`
  -- unfold matrix.mul,
  show_term {change (A)⁻¹ ⬝ A = 1},
  rw matrix.nonsing_inv_mul A (symplectic_det A.prop),
  end,
  .. submonoid.to_monoid _ }
  
end symplectic_group

end

-- TODO: Add this back in 
-- def symplectic_transpose : symplectic l → symplectic l := fun A, 
-- { val := Aᵀ,
--   property :=
--   begin 
--    sorry
--   end }