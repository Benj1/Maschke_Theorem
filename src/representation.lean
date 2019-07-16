-- This library contains proofs of basic facts in the representation theory of groups.
-- The definition of a representation is given outside of any namespace. The namespaces are:
-- monoid_module, fixed_points, monoid_representation, group_representation.
-- Author: Ben McDonnell
-- TODO: 1) Repitition of theory between group_representation and monoid_representation
--       2) Most lemmas in group_representation.map are in fact lemmas about linear_maps and are 
--            (probably) already written elsewhere.
--       3) Each step in the proof of Schur's lemma is a useful general fact. E.g. ker f = top implies f = 0
--       4) New representations from old

import algebra.module
import group_theory.group_action
import group_theory.subgroup
import group_theory.submonoid
import linear_algebra.basic

/-- A monoid module is a G-representation M, over the ring of integers -/
class monoid_module (G M : Type) [monoid G] [add_comm_group M]
  extends mul_action G M :=
(smul_add : ∀ (g : G) (m₁ m₂ : M), g • (m₁ + m₂) = g • m₁ + g • m₂)

attribute [simp] monoid_module.smul_add

/-- A monoid representation is a G-representation M over an arbitrary ring R -/
class monoid_representation (G R M : Type) [monoid G] [ring R] [add_comm_group M] [module R M]
  extends monoid_module G M :=
(smul_comm : ∀ (g : G) (r : R) (m : M), g • (r • m) = r • (g • m))

/-- group_represention restricts the defintion of monoid representation to only allow G a group -/
class group_representation (G R M : Type) [group G] [ring R] [add_comm_group M] [module R M]
  extends monoid_representation G R M

----------------------------
namespace monoid_module
variables (G : Type) {M N : Type} [monoid G] [add_comm_group M] [monoid_module G M]
variables [add_comm_group N] [monoid_module G N]

variable (M)
/-- G acts on 0 trivially -/
lemma smul_zero_ : ∀ (g : G), g • (0 : M) = (0 : M) := λ g, 
begin
  have : g • (0 : M) + g • 0 = g • 0 := by rw [← monoid_module.smul_add, add_zero],
  simp * at *,
end

/-- Any instance of a monoid module will create an instance of a distrib_mul_action -/
instance : distrib_mul_action G M :=
{ smul := λ g m, g • m,
  one_smul := mul_action.one_smul G,
  mul_smul := mul_action.mul_smul,
  smul_add := monoid_module.smul_add,
  smul_zero := smul_zero_ G M}

variable {M}

/-- A homomorphism of monoid_modules respects additivity and smul -/
structure map :=
(to_fun : M → N)
(add : ∀ (x y : M), to_fun (x + y) = to_fun x + to_fun y)
(smul : ∀ (g : G) (x : M), to_fun(g • x) = g • to_fun x)

/-- Given a map to_fun, we need to prove additivity and smul to show it is a monoid_module map -/
class is_map (to_fun : M → N) :=
(add : ∀ (x y : M), to_fun (x + y) = to_fun x + to_fun y)
(smul : ∀ (g : G) (x : M), to_fun(g • x) = g • to_fun x)
end monoid_module

----------------------------
namespace fixed_points
open mul_action
variables {G M : Type} [monoid G] [add_comm_group M] [monoid_module G M]

lemma add_mem (x y : M) (hx : x ∈ fixed_points G M) (hy : y ∈ fixed_points G M) :
  x + y ∈ fixed_points G M :=
begin
  intro g,
  simp only [mem_stabilizer_iff, monoid_module.smul_add, mem_fixed_points] at *,
  rw [hx g, hy g],
end

end fixed_points

----------------------------
namespace monoid_representation
variables (G R M : Type)
variables [monoid G] [ring R] [add_comm_group M] [module R M] [monoid_representation G R M]

/-- Given a group G, ring R and R-module M, we can always define the trivial representation on M,
  such that G acts by the identity -/
def trivial : monoid_representation G R M := 
{ smul := λ (g : G) (m : M), m,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl,
  smul_add := λ _ _ _, rfl,
  smul_comm := λ _ _ _, rfl}
 
variable {G}
/-- The structure map of (g : G) is the endomorphism of M given by the smul action of g -/
def structure_map (g : G) : M →ₗ[R] M := 
{ to_fun := λ m, g • m,
  add := λ x y, monoid_module.smul_add g x y,
  smul := λ r x, monoid_representation.smul_comm g r x }

@[simp] lemma structure_map_mul (g₁ g₂ : G) :
  structure_map R M (g₁ * g₂) = structure_map R M g₁ * structure_map R M g₂ :=
begin
  apply linear_map.ext,
  intro x,
  -- show (g₁ * g₂) • x = g₁ • g₂ • x,
  apply mul_action.mul_smul,
end
variables {R} {M}

variable (G)
/-- A submodule is a subrepresentation if it is stable under the G action -/
class is_subrepresentation (N : submodule R M) : Prop := 
(closed : ∀ (g : G) (n : M), n ∈ N → g • n ∈ N)

variable {G}
/-- Any representation is a subrepresentation of itself -/
instance : is_subrepresentation G (⊤ : submodule R M) := 
{closed := λ g m hm, by simp,}

/-- Every representation has {0} as a subrepresentation -/
lemma zero_is_subrepresentation : is_subrepresentation G (⊥ : submodule R M) := 
{ closed := λ g n h, begin simp at *, rw h, exact smul_zero g, end }

/-- A subrepresentation is in a representation in its own right -/
instance subrepresentation.to_representation (N : submodule R M) [is_subrepresentation G N] : 
  monoid_representation G R N := sorry

include R M -- inclusion somehow solves class resolution
/-- The kernel of a representation consists of all elements of G which act on M trivially -/
def kernel : set G := {g | ∀ (m : M), g • m = m}
omit R M

@[simp] lemma mem_kernel_iff {g : G} :
  g ∈ (@kernel G R M _ _ _ _ _) ↔ ∀ (m : M), g • m = m := iff.rfl

/-- A proof that the kernel is indeed a submonoid of G -/
instance kernel.to_submonoid : is_submonoid (@kernel G R M _ _ _ _ _)  := 
{ one_mem := iff.elim_right mem_kernel_iff (mul_action.one_smul G),
  mul_mem := begin
  intros,
  apply iff.elim_right mem_kernel_iff,
  intro,
  rw mul_action.mul_smul,
  rw mem_kernel_iff at a_1 a_2,
  rw a_2,
  exact a_1 m,
  end }

variables (G) (R) (M)
/-- A representation is irreducible if the only subrepresentaitons are itself and {0} -/
def is_irreducible : Prop := ∀ (L : submodule R M), is_subrepresentation G L → (L = ⊤) ∨ (L = ⊥)
variables {G} {R} {M}

/-- A homomorphism of monoid representations is a linear map which respects the G action -/
class is_map {N : Type} [add_comm_group N] [module R N] [monoid_representation G R N]
  (to_fun : M → N) extends is_linear_map R to_fun :=
(gmul : ∀ (g : G) (m : M), to_fun(g • m) = g • to_fun m) 
variable {G}

--set_option pp.all true

include G
/-- A monoid representation of a group G can be upgraded to a group representation -/
instance [group G] : group_representation G R M := 
{ smul := λ g m, g • m,
  one_smul := sorry,
  mul_smul := sorry,
  smul_add := sorry,
  smul_comm := sorry }
omit G

---------------------------- (sub namespace of monoid_representation)
namespace map
-- Introduce a second representation N and a G-map f : M → N 
variables {N : Type} [add_comm_group N] [module R N] [monoid_representation G R N] 
variables (f : M → N) [is_linear_map R f] [@is_map G R M _ _ _ _ _ N _ _ _ f]

/-- The kernel of a G-homomorphism is the R-submodule of elements which map to zero -/
def kernel : submodule R M := 
{ carrier := {m | f m = 0},
  zero := begin show f 0 = 0, exact @is_linear_map.map_zero R M N _ _ _ _ _ f _inst_9, end,
  add := λ x y hx hy, begin simp * at *, rw @is_linear_map.add R M N _ _ _ _ _ f _ x y, rw [hx, hy], 
    exact add_zero 0, end,
  smul := λ r m hm,  begin simp * at *, rw [@is_linear_map.smul R M N _ _ _ _ _ f _ r m, hm],
    exact @distrib_mul_action.smul_zero R N _ _ (semimodule.to_distrib_mul_action R N) r,
  end
}

@[simp] lemma mem_kernel_iff {m : M} : m ∈ (@kernel R M _ _ _ N _ _ f _) ↔ f m = 0 := iff.rfl 

/-- If f a = f b, then a-b is in the kernel. -/
lemma equal_image_mem_kernel : ∀ (m₁ m₂ : M), f m₁ = f m₂ → m₁ - m₂ ∈ (@kernel R M _ _ _ N _ _ f _):= 
λ m₁ m₂ h, by {
simp,
rw (is_linear_map.add R f m₁ (-m₂)),
replace h := congr_arg (λ x, x + f (-m₂)) h,
dsimp at h,
rw ← (is_linear_map.add R f m₂ (-m₂)) at h,
simp at h,
rw (@is_linear_map.map_zero R M N _ _ _ _ _ f _inst_9) at h,
assumption,
}

/-- The image of a G-homomorphism is the R-submodule of elements which can be written as f m for some m. -/
def image : submodule R N := { carrier := {n | ∃ (m : M), f m = n},
  zero := begin show ∃ (m : M), f m = 0, existsi (0 : M), 
    exact @is_linear_map.map_zero R M N _ _ _ _ _ f _inst_9, end,
  add := λ x y hx hy, begin simp * at *, cases hx with m₁ hm₁, cases hy with m₂ hm₂, 
    have : f(m₁ + m₂) = x + y := by {rw [@is_linear_map.add R M N _ _ _ _ _ f _ m₁ m₂, hm₁, hm₂]},
    existsi m₁ + m₂,
    exact this, end,
  smul := λ r n hn, begin simp * at *, cases hn with m hn,     
    -- Forcing LEAN to recognise the scalar multiplication R M
    have _inst_Mscalar : has_scalar R M := { smul := @has_scalar.smul R M (@mul_action.to_has_scalar R M _ 
      (@distrib_mul_action.to_mul_action R M _ _ (semimodule.to_distrib_mul_action R M)))},
    -- Forcing LEAN to recognise the scalar multiplication R N
    have _inst_Nscalar : has_scalar R N := { smul := @has_scalar.smul R N (@mul_action.to_has_scalar R N _ 
      (@distrib_mul_action.to_mul_action R N _ _ (semimodule.to_distrib_mul_action R N)))},
    -- No • notation here to force class resolution
    existsi @has_scalar.smul R M _inst_Mscalar r m,
    have step1 : @has_scalar.smul R N _inst_Nscalar r (f m) = @has_scalar.smul R N _inst_Nscalar r n, by {rw hn,},
    -- Something is going very wrong here
    have goal : f (@has_scalar.smul R M _inst_Mscalar r m) = @has_scalar.smul R N _inst_Nscalar r n, by {
      rw ← step1,
      -- now apply linearmap.smul
      sorry,},
    sorry,
  end
}

@[simp] lemma mem_image_iff {n : N} : n ∈ (@image R M _ _ _ N _ _ f _) ↔ ∃ (m : M), f m = n := iff.rfl

/-- A silly lemma that f m is in the image of f -/
@[simp] lemma image_mem_image :  ∀ (m : M), f m ∈ (@image R M _ _ _ N _ _ f _) := λ m, by {
simp,
existsi m,
reflexivity,
}

/-- The kernel of a map is a sub-representation of the source -/
instance kernel.to_subrepresentation : is_subrepresentation G (@kernel R M _ _ _ N _ _ f _) := 
{ closed := λ g m hm, begin simp * at *, 
    rw [@is_map.gmul G R M _ _ _ _ _ N _ _ _ f _ g m, hm, monoid_module.smul_zero_], end}

/-- The image of a map is a sub-representation of the target -/
instance image.to_subrepresentation : is_subrepresentation G (@image R M _ _ _ N _ _ f _) := 
{ closed := λ g n hn, begin simp * at *, cases hn with m hm, existsi g • m, 
    rw [@is_map.gmul G R M _ _ _ _ _ N _ _ _ f _ g m, hm], end}

/-- The general version of Schur's lemma, namely that a map f : irrep → irrep is either 0 or an isomorphism -/
lemma of_irreducibles : is_irreducible G R M → is_irreducible G R N → f = (λ m, 0) ∨ function.bijective f := 
begin
intros hM hN,
-- Since M and N are irreducible, both the kernel and image are trivial (i.e. \top or \bot)
have h_kernel : (@kernel R M _ _ _ N _ _ f _) = (⊤ : submodule R M) ∨ (@kernel R M _ _ _ N _ _ f _) = (⊥ : submodule R M):=
  hM (@kernel R M _ _ _ N _ _ f _) (kernel.to_subrepresentation f),
have h_image : (@image R M _ _ _ N _ _ f _) = (⊤ : submodule R N) ∨ (@image R M _ _ _ N _ _ f _) = (⊥ : submodule R N):=
  hN (@image R M _ _ _ N _ _ f _) (image.to_subrepresentation f),
-- First suppose the kernel is M. We will then prove that f is zero.
cases h_kernel,
have : f = (λ m, 0) := by {apply funext, intro m, 
  have hm_top : (m : M) ∈ (⊤ : submodule R M) := by simp,
  have hm_kernel : m ∈ kernel f := by {rw h_kernel, assumption},
  simpa,
},
left, assumption, 
-- We have just proved that if ker = ⊤ then f = 0. 
-- Next we split into cases for the image. Then first show that image=0 means f=0.
cases h_image,
swap,
have : f = (λ m, 0) := by {
  apply funext,
  intro m,
  have fm_mem_im : f m ∈ image f := image_mem_image f m,
  rw h_image at fm_mem_im,
  simp * at *,
},
left, assumption,
-- Now we are in the final case, ker = 0 and the image is everything.
-- We first show that zero kernel implies injective.
have hf_inj : function.injective f := by { show ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂,
  intros a b hab,
  have ab_mem : a - b ∈ kernel f := equal_image_mem_kernel f a b hab,
  rw h_kernel at ab_mem,
  simp at ab_mem,
  replace ab_mem := congr_arg (λ x, x + b) ab_mem,
  simp at ab_mem,
  assumption,
},
right,
-- We then show that image everything implies surjective.
have hf_sur : function.surjective f := by {show ∀ n, ∃ m, f m = n, intro m, 
  have m_in_top : m ∈ (⊤ : submodule R N) := by simp,
  rw ← h_image at m_in_top,
  simpa,
},
-- Finally, injective + bijective = bijective.
constructor, assumption, assumption,
end
end map -- end of the subnamespace

end monoid_representation


----------------------------
namespace group_representation
variables (G R M : Type)
variables [group G] [ring R] [add_comm_group M] [module R M] [group_representation G R M]

/-- The trivial group representation is the trivial monoid representation structure on G R M, but extended to 
a group representation -/
def trivial : group_representation G R M := 
  @monoid_representation.group_representation G R M _ _ _ _ (monoid_representation.trivial G R M) _

variables {R} {M}
/-- A submodule is a subrepresentation if it is stable under the G action -/
class is_subrepresentation (N : submodule R M) : Prop := 
(closed : ∀ (g : G) (n : M), n ∈ N → g • n ∈ N)

variable {G}
/-- Any representation is a subrepresentation of itself -/
instance : is_subrepresentation G (⊤ : submodule R M) := 
{closed := λ g m hm, by simp,}

/-- Every representation has {0} as a subrepresentation -/
lemma zero_is_subrepresentation : is_subrepresentation G (⊥ : submodule R M) := 
{ closed := λ g n h, begin simp at *, rw h, exact smul_zero g, end }

/-- A subrepresentation is in a representation in its own right -/
instance subrepresentation.to_representation (N : submodule R M) [is_subrepresentation G N] : 
  group_representation G R N := sorry

/-- The kernel of a representation consists of all elements of G which act on M trivially -/
def kernel : set G := @monoid_representation.kernel G R M _ _ _ _ _

lemma mem_kernel_iff {g : G} :
  g ∈ (@kernel G R M _ _ _ _ _) ↔ ∀ (m : M), g • m = m := iff.rfl 

/-- A proof that the kernel is indeed a subgroup of G -/
instance kernel.to_subgroup : is_subgroup (@kernel G R M _ _ _ _ _) := 
{ one_mem := iff.elim_right mem_kernel_iff (mul_action.one_smul G),
  mul_mem := begin
  intros,
  rw mem_kernel_iff,
  intro,
  rw mul_action.mul_smul,
  rw mem_kernel_iff at a_1 a_2,
  rw a_2,
  exact a_1 m,
  end,
  inv_mem := begin
  intros g h,
  rw mem_kernel_iff,
  intro,
  rw mem_kernel_iff at h,
  replace h := h m,
  replace h := congr_arg (λ (x : M), g⁻¹ • x) h,
  dsimp at h,
  rw [← mul_action.mul_smul] at h,
  by simp [h.symm],
  end }

variables (R) (M)
include R M 
/-- A proof that m ↦ g⁻¹ m is a left inverse of the structure map -/
lemma structure_map.left_inverse (g : G) : function.left_inverse (λ (m : M), g⁻¹ • m) (λ (m : M), g • m) :=
begin
intro m,
show g⁻¹ • g • m = m,
rw ← mul_action.mul_smul,
simp,
end 
/-- A proof that m ↦ g⁻¹ m is a right inverse of the structure map -/
lemma structure_map.right_inverse (g : G) : function.right_inverse (λ (m : M), g⁻¹ • m) (λ (m : M), g • m) :=
begin
intro m,
show g • g⁻¹ • m = m,
rw ← mul_action.mul_smul,
simp,
end 
omit R M 

variables (G)
def is_irreducible : Prop := ∀ (L : submodule R M), is_subrepresentation G L → (L = ⊤) ∨ (L = ⊥)
variables {G} {R} {M}

/-- A G-homomorphism between representations is an R-linear map which respects the G action -/
class is_map {N : Type} [add_comm_group N] [module R N] [group_representation G R N] (f : M → N ) 
  extends is_linear_map R f :=
(gmul : ∀ (g : G) (m : M), f (g • m) = g • (f m) )

---------------------------- (sub namespace of group_representation)
namespace map
-- Introduce a second representation N and a G-map f : M → N 
variables {N : Type} [add_comm_group N] [module R N] [group_representation G R N] 
variables (f : M → N) [is_linear_map R f] [@is_map G R M _ _ _ _ _ N _ _ _ f]

/-- The kernel of a G-homomorphism is the R-submodule of elements which map to zero -/
def kernel : submodule R M := 
{ carrier := {m | f m = 0},
  zero := begin show f 0 = 0, exact @is_linear_map.map_zero R M N _ _ _ _ _ f _inst_9, end,
  add := λ x y hx hy, begin simp * at *, rw @is_linear_map.add R M N _ _ _ _ _ f _ x y, rw [hx, hy], 
    exact add_zero 0, end,
  smul := λ r m hm,  begin simp * at *, rw [@is_linear_map.smul R M N _ _ _ _ _ f _ r m, hm],
    exact @distrib_mul_action.smul_zero R N _ _ (semimodule.to_distrib_mul_action R N) r,
  end
}

@[simp] lemma mem_kernel_iff {m : M} : m ∈ (@kernel R M _ _ _ N _ _ f _) ↔ f m = 0 := iff.rfl 

/-- If f a = f b, then a-b is in the kernel. -/
lemma equal_image_mem_kernel : ∀ (m₁ m₂ : M), f m₁ = f m₂ → m₁ - m₂ ∈ (@kernel R M _ _ _ N _ _ f _):= 
λ m₁ m₂ h, by {
simp,
rw (is_linear_map.add R f m₁ (-m₂)),
replace h := congr_arg (λ x, x + f (-m₂)) h,
dsimp at h,
rw ← (is_linear_map.add R f m₂ (-m₂)) at h,
simp at h,
rw (@is_linear_map.map_zero R M N _ _ _ _ _ f _inst_9) at h,
assumption,
}

/-- The image of a G-homomorphism is the R-submodule of elements which can be written as f m for some m. -/
def image : submodule R N := { carrier := {n | ∃ (m : M), f m = n},
  zero := begin show ∃ (m : M), f m = 0, existsi (0 : M), 
    exact @is_linear_map.map_zero R M N _ _ _ _ _ f _inst_9, end,
  add := λ x y hx hy, begin simp * at *, cases hx with m₁ hm₁, cases hy with m₂ hm₂, 
    have : f(m₁ + m₂) = x + y := by {rw [@is_linear_map.add R M N _ _ _ _ _ f _ m₁ m₂, hm₁, hm₂]},
    existsi m₁ + m₂,
    exact this, end,
  smul := λ r n hn, begin simp * at *, cases hn with m hn,     
    -- Forcing LEAN to recognise the scalar multiplication R M
    have _inst_Mscalar : has_scalar R M := { smul := @has_scalar.smul R M (@mul_action.to_has_scalar R M _ 
      (@distrib_mul_action.to_mul_action R M _ _ (semimodule.to_distrib_mul_action R M)))},
    -- Forcing LEAN to recognise the scalar multiplication R N
    have _inst_Nscalar : has_scalar R N := { smul := @has_scalar.smul R N (@mul_action.to_has_scalar R N _ 
      (@distrib_mul_action.to_mul_action R N _ _ (semimodule.to_distrib_mul_action R N)))},
    -- No • notation here to force class resolution
    existsi @has_scalar.smul R M _inst_Mscalar r m,
    have step1 : @has_scalar.smul R N _inst_Nscalar r (f m) = @has_scalar.smul R N _inst_Nscalar r n, by {rw hn,},
    -- Something is going very wrong here
    have goal : f (@has_scalar.smul R M _inst_Mscalar r m) = @has_scalar.smul R N _inst_Nscalar r n, by {
      rw ← step1,
      -- now apply linearmap.smul
      sorry,},
    sorry,
  end
}

@[simp] lemma mem_image_iff {n : N} : n ∈ (@image R M _ _ _ N _ _ f _) ↔ ∃ (m : M), f m = n := iff.rfl

/-- A silly lemma that f m is in the image of f -/
@[simp] lemma image_mem_image :  ∀ (m : M), f m ∈ (@image R M _ _ _ N _ _ f _) := λ m, by {
simp,
existsi m,
reflexivity,
}

/-- The kernel of a map is a sub-representation of the source -/
instance kernel.to_subrepresentation : is_subrepresentation G (@kernel R M _ _ _ N _ _ f _) := 
{ closed := λ g m hm, begin simp * at *, 
    rw [@is_map.gmul G R M _ _ _ _ _ N _ _ _ f _ g m, hm, monoid_module.smul_zero_], end}

/-- The image of a map is a sub-representation of the target -/
instance image.to_subrepresentation : is_subrepresentation G (@image R M _ _ _ N _ _ f _) := 
{ closed := λ g n hn, begin simp * at *, cases hn with m hm, existsi g • m, 
    rw [@is_map.gmul G R M _ _ _ _ _ N _ _ _ f _ g m, hm], end}

/-- The general version of Schur's lemma, namely that a map f : irrep → irrep is either 0 or an isomorphism -/
lemma of_irreducibles : is_irreducible G R M → is_irreducible G R N → f = (λ m, 0) ∨ function.bijective f := 
begin
intros hM hN,
-- Since M and N are irreducible, both the kernel and image are trivial (i.e. \top or \bot)
have h_kernel : (@kernel R M _ _ _ N _ _ f _) = (⊤ : submodule R M) ∨ (@kernel R M _ _ _ N _ _ f _) = (⊥ : submodule R M):=
  hM (@kernel R M _ _ _ N _ _ f _) (kernel.to_subrepresentation f),
have h_image : (@image R M _ _ _ N _ _ f _) = (⊤ : submodule R N) ∨ (@image R M _ _ _ N _ _ f _) = (⊥ : submodule R N):=
  hN (@image R M _ _ _ N _ _ f _) (image.to_subrepresentation f),
-- First suppose the kernel is M. We will then prove that f is zero.
cases h_kernel,
have : f = (λ m, 0) := by {apply funext, intro m, 
  have hm_top : (m : M) ∈ (⊤ : submodule R M) := by simp,
  have hm_kernel : m ∈ kernel f := by {rw h_kernel, assumption},
  simpa,
},
left, assumption, 
-- We have just proved that if ker = ⊤ then f = 0. 
-- Next we split into cases for the image. Then first show that image=0 means f=0.
cases h_image,
swap,
have : f = (λ m, 0) := by {
  apply funext,
  intro m,
  have fm_mem_im : f m ∈ image f := image_mem_image f m,
  rw h_image at fm_mem_im,
  simp * at *,
},
left, assumption,
-- Now we are in the final case, ker = 0 and the image is everything.
-- We first show that zero kernel implies injective.
have hf_inj : function.injective f := by { show ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂,
  intros a b hab,
  have ab_mem : a - b ∈ kernel f := equal_image_mem_kernel f a b hab,
  rw h_kernel at ab_mem,
  simp at ab_mem,
  replace ab_mem := congr_arg (λ x, x + b) ab_mem,
  simp at ab_mem,
  assumption,
},
right,
-- We then show that image everything implies surjective.
have hf_sur : function.surjective f := by {show ∀ n, ∃ m, f m = n, intro m, 
  have m_in_top : m ∈ (⊤ : submodule R N) := by simp,
  rw ← h_image at m_in_top,
  simpa,
},
-- Finally, injective + bijective = bijective.
constructor, assumption, assumption,
end
end map -- end of the subnamespace

----------------- Show that the structure map defines a group homomorphism ---------
-- -- A representation is a group hom from G to GL_R(M). This map will be called the structure map.
-- def structure_map (g : G) : M ≃ₗ[R] M :=
-- { to_fun := λ m, g • m,
--   add := monoid_module.gmul_add g,
--   smul := monoid_representation.gmul_comm g,
--   inv_fun := λ m, g⁻¹ • m,
--   left_inv := λ m, by { dsimp, rw [← mul_action.mul_gmul, mul_left_inv, mul_action.one_gmul] },
--   right_inv := λ m, by { dsimp, rw [← mul_action.mul_gmul, mul_right_inv, mul_action.one_gmul] } }

-- variables {R}{M} -- Forget the explicit R and M

-- -- this should go to another file
-- lemma linear_equiv.ext (f g : M ≃ₗ[R] M) (H : (f : M → M) = (g : M → M)) : f = g :=
-- begin
--   cases f, cases g,
--   congr,
--   { exact H },
--   { funext m,
--     change f_to_fun = g_to_fun at H,
--     dsimp [function.left_inverse, function.right_inverse] at *,
--     rw H at f_left_inv,
--     have : function.surjective g_to_fun :=
--     begin
--       apply function.surjective_of_has_right_inverse,
--       delta function.has_right_inverse,
--       use g_inv_fun,
--       exact g_right_inv
--     end,
--     rcases this m with ⟨m, rfl⟩,
--     simp *, }
-- end

-- instance : group (M ≃ₗ[R] M) :=
-- { mul := λ f g, g.trans f,
--   mul_assoc := by { intros f g h, cases f, cases g, cases h, dsimp [linear_equiv.trans], congr' 1 },
--   one := linear_equiv.refl _,
--   one_mul := by { intro f, cases f, dsimp [linear_equiv.trans], congr' 1 },
--   mul_one := by { intro f, cases f, dsimp [linear_equiv.trans, linear_equiv.refl, (*)], congr' 1 },
--   inv := linear_equiv.symm,
--   mul_left_inv := by { intro f, cases f, dsimp [linear_equiv.trans, (*)], sorry } }

-- @[simp] lemma linear_equiv.mul_apply (f g : M ≃ₗ[R] M) (m : M) : (f * g) m = f (g m) := rfl

-- @[simp] lemma structure_map_mul (g₁ g₂ : G) :
--   structure_map R M (g₁ * g₂) = structure_map R M g₁ * structure_map R M g₂ :=
-- begin
--   apply linear_equiv.ext,
--   funext m,
--   show (g₁ * g₂) • m = g₁ • (g₂ • m),
--   rw mul_action.mul_smul
-- end

-- instance structure_map_is_group_hom : is_group_hom (structure_map R M : G → (M ≃ₗ[R] M)) :=
-- { map_mul := λ g₁ g₂, by simp }

-- @[simp] lemma structure_map_one : structure_map R M (1 : G) = 1 := is_group_hom.map_one _
-- @[simp] lemma structure_map_inv (g : G) :
--   structure_map R M (g⁻¹ : G) = (structure_map R M g)⁻¹ :=
-- is_group_hom.map_inv _ _

end group_representation