import algebra.module
import data.set.function
import linear_algebra.direct_sum_module
import linear_algebra.basic

namespace linear_map
variables (R : Type) {L M N : Type} [ring R] [add_comm_group M] [module R M]
variables [add_comm_group L] [module R L] 
variables [add_comm_group N] [module R N]
variables (g : M → N) (f : L → M) [is_linear_map R g] [is_linear_map R f]

/-- Given two is_linear maps, the composition is a linear map -/
def linear_composition : linear_map R L N := 
{ to_fun := (g ∘ f),
  add := λ x y, 
    begin simp, conv_lhs {congr, rw @is_linear_map.add R L M _ _ _ _ _ f _},
    conv_lhs {rw @is_linear_map.add R M N _ _ _ _ _ g _},
    end,
  smul := λ r x, begin simp, conv_lhs {congr,  rw @is_linear_map.smul R L M _ _ _ _ _ f _,},
    conv_lhs {rw @is_linear_map.smul R M N _ _ _ _ _ g _},
    end
}

/-- Given two is_linear maps, the composition is an is_linear map -/
def is_linear_composition : is_linear_map R (g ∘ f) := 
{ add := λ x y, 
    begin simp, conv_lhs {congr, rw @is_linear_map.add R L M _ _ _ _ _ f _},
    conv_lhs {rw @is_linear_map.add R M N _ _ _ _ _ g _},
    end,
  smul := λ r x, begin simp, conv_lhs {congr,  rw @is_linear_map.smul R L M _ _ _ _ _ f _,},
    conv_lhs {rw @is_linear_map.smul R M N _ _ _ _ _ g _},
    end
}

end linear_map

----------------------------
namespace submodule
variables {R : Type} {M : Type} [ring R] [add_comm_group M] [module R M]
variables (L N : submodule R M)

/-- The sum of two submodules L and N is again a submodule L + N -/
def sum : submodule R M := 
{ carrier := {m | ∃ (x : L) (y : N), m = x + y},
  zero := begin simp, existsi [(0 : L), (0 : N)], simp, end,
  add := λ x y, begin intros hx hy, simp * at *, 
    cases hx with x₁ hhx,
    cases hhx with x₂ sum_x,
    cases hy with y₁ hhy,
    cases hhy with y₂ sum_y,
    existsi [x₁ + y₁, x₂ + y₂],
    simp * at *,
    end,
  smul := λ r m, begin intro hm, simp * at *,
    cases hm with x hh,
    cases hh with y sum_m,
    existsi [r • x, r • y],
    rw sum_m,
    rw distrib_mul_action.smul_add,
    simp,
    end,}

/-- A simplification lemma to give a condition on being a member of the sum -/
@[simp] lemma mem_sum_iff (m : M) : 
  m ∈ sum L N ↔ ∃ (x : L) (y : N), m = x + y := iff.rfl

/-- There is a map (which is an iso when L ⊓ N = 0) from L × N → M, given by addition -/
def direct_map : L × N →ₗ[R] M := 
{ to_fun := λ x, (x.fst : M) + (x.snd : M),
  add := λ x, by simp,
  smul := λ r x, begin simp, rw smul_add, end }

@[simp] lemma direct_map_to_fun (x : L × N) : 
  direct_map L N x = (x.fst : M) + (x.snd : M) := rfl

/-- The intersection of L and N includes diagonally into L × N -/
def diagonal_inclusion : L ⊓ N → L := λ x, sorry

/-- The kernel of the direct_map is the intersection of L and N -/
lemma direct_map_ker : (direct_map L N).ker = 0 := sorry

/-- The image of the direct map is the sum of the submodules L and N -/
lemma direct_map_range : (direct_map L N).range = sum L N := begin
ext,
apply iff.intro,
repeat {  -- The forward and converse directions have the same proof
intro hx,
simp * at *,
cases hx with a hhx,
cases hhx with b hab,
existsi [a, b],
rw hab,},
end

end submodule

----------------------------
namespace module
variables {R : Type} {M : Type} [ring R] [add_comm_group M] [module R M]

variables (R) (M)
/-- A module M decomposes if there exist L and N such that the direct map is a 
bijection. It follows that L × N ≃ M -/
def decomposes : Prop := ∃ (L N : submodule R M), (submodule.direct_map L N).ker = ⊥
 ∧ (submodule.direct_map L N).range = ⊤

end module

----------------------------
namespace short_exact
-- First introduce a sequence L → M → N of G-homomorphisms
variables (R : Type) {L M N : Type} [ring R] [add_comm_group M] [module R M]
variables [add_comm_group L] [module R L] 
variables [add_comm_group N] [module R N]
variables (φ : L →ₗ[R] M) (ψ : M →ₗ[R] N)

/-- A SES is sequence φ: L → M, ψ : M → N such that φ is injective, ψ surjective and kerψ = imφ -/
def is_short_exact_sequence : Prop :=
(function.injective φ) ∧ (function.surjective ψ) ∧ (ψ.ker = φ.range)

-- Introduce a proof that our sequence is in fact a SES
variable [is_short_exact_sequence R φ ψ]

/-- A splitting map is a map s : N → M such that ψ ∘ s is the identity on N -/
def splitting_map (s : N →ₗ[R] M) : Prop := function.left_inverse ψ s

/-- A retraction map is a map r : M → L such that r ∘ φ is the identity on L -/
def retraction_map (r : M →ₗ[R] L) : Prop := function.left_inverse r φ

end short_exact