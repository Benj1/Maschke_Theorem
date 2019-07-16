-- ----------------------------
-- -- This section defines the external direct sum. Namely given two modules
-- -- the product M × N has a module structure
-- namespace direct_sum
-- variables (R : Type) (M N : Type) [ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N]

-- /-- Endow M × N with additive abelian group structure, with component-wise addition -/
-- instance : add_comm_group (M × N) := 
-- { add := λ a, λ b, ⟨a.fst + b.fst, a.snd + b.snd⟩,
--   add_assoc := λ a b c, by simp,
--   zero := ⟨0, 0⟩,
--   zero_add := λ a, by simp,
--   add_zero := λ a, prod.rec_on a (λ a₁ a₂, begin show (a₁ + 0, a₂ + 0) = (a₁, a₂), simp, end),
--   neg := λ a, prod.rec_on a (λ a₁ a₂, ⟨-a₁, -a₂⟩),
--   add_left_neg := λ a, prod.rec_on a (λ a₁ a₂, begin  show (-a₁ + a₁, -a₂ + a₂) = (0,0), simp, end ) ,
--   add_comm := λ a b, prod.rec_on a 
--     (λ a₁ a₂, prod.rec_on b (λ b₁ b₂, begin show (a₁ + b₁, a₂ + b₂) = (b₁ + a₁, b₂ + a₂), simp, end ))}

-- /-- Projection onto the first coordinate -/
-- def project_fst : M × N → M := (λ (x : M × N), x.fst) 

-- /-- Projection onto the second coordinate -/
-- def project_snd : M × N → N := (λ (x : M × N), x.snd)

-- /-- Define the inclusion map to the first component -/
-- def include_fst : M → M × N := λ m, ⟨m, 0⟩

-- /-- Define the inclusion map to the second component -/
-- def include_snd : N → M × N := λ n, ⟨0, n⟩

-- /-- The inclusion map to the first component is additive -/
-- @[simp] lemma include_fst_add (x y : M): ((x + y, 0) : M × N) = (x, 0) + (y, 0) := 
-- begin 
-- let a : M × N := (x, 0),
-- let b : M × N := (y, 0),
-- let sum : M × N := ⟨a.fst + b.fst, a.snd + b.snd⟩,
-- conv_rhs {change sum},
-- simp,
-- end

-- /-- The inlcusion map to the second component is additive -/
-- @[simp] lemma include_snd_add (x y : N): ((0, x + y) : M × N) = (0, x) + (0, y) := 
-- begin 
-- let a : M × N := (0, x),
-- let b : M × N := (0, y),
-- let sum : M × N := ⟨a.fst + b.fst, a.snd + b.snd⟩,
-- conv_rhs {change sum},
-- simp,
-- end

-- /-- The projection onto the first coordinate is an additive map -/
-- @[simp] lemma fst_additivity (x y : M × N) : (x + y).fst = x.fst + y.fst := by finish

-- /-- The projection onto the second coordinate is an additive map -/
-- @[simp] lemma snd_additivity (x y : M × N) : (x + y).snd = x.snd + y.snd := by finish

-- /-- Give M × N an R-module structure -/
-- instance : module R (M × N) := 
-- { smul := λ r a, ⟨r • a.fst, r • a.snd⟩,
--   one_smul := λ x, by simp,
--   mul_smul := λ r₁ r₂ x, begin simp, split, repeat {rw mul_action.mul_smul}, end, 
--   smul_add := λ r x y, begin simp, rw distrib_mul_action.smul_add,
--     rw @distrib_mul_action.smul_add R N _ _ _ r x.snd y.snd, finish,
--     end,
--   smul_zero := λ r, begin
--     simp,
--     conv_lhs {change (r • (0 : M), r • (0 : N)),},
--     finish,
--     end,
--   add_smul := λ r s x, prod.rec_on x (λ x₁ x₂, begin 
--     simp,
--     conv_lhs {congr, rw semimodule.add_smul, skip, rw semimodule.add_smul,},
--     show (r • x₁ , r • x₂) + (s • x₁, s • x₂) = (r • x₁, r • x₂) + (s • x₁, s • x₂),
--     finish,
--     end),
--   zero_smul := λ x, by finish, 
-- }

-- /-- The projection onto the first coordinate respects the scalar multiplication -/
-- @[simp] lemma fst_smul : ∀ (r : R) (x : M × N), (r • x).fst = r • x.fst := λ r x, prod.rec_on x (λ x₁ x₂,
-- by finish)

-- /-- The projection onto the second coordinate respects the scalar multiplication -/
-- @[simp] lemma snd_smul : ∀ (r : R) (x : M × N), (r • x).snd = r • x.snd := λ r x, prod.rec_on x (λ x₁ x₂,
-- by finish)

-- /-- The inclusion to the first coordinate respects the scalar multiplication -/
-- lemma include_fst_smul : ∀ (r : R) (x : M), (r • x, (0 : N)) = r • (x, 0) :=
-- λ r x,
-- begin
-- let a := (x, (0 : N)),
-- let smul := (r • a.fst, r • a.snd),
-- conv_rhs {change smul},
-- simp,
-- end

-- /-- The inclusion to the second coordinate respects the scalar multiplication -/
-- lemma include_snd_smul : ∀ (r : R) (x : N), ((0 : M), r • x) = r • (0, x) :=
-- λ r x,
-- begin
-- let a := ((0 : M), x),
-- let smul := (r • a.fst, r • a.snd),
-- conv_rhs {change smul},
-- simp,
-- end

-- /-- The projection onto the first coordinate is a linear map -/
-- instance fst_linear : is_linear_map R (project_fst M N) := 
-- { add := λ x y, fst_additivity M N x y,
--   smul := λ r x, fst_smul R M N r x,
-- }

-- /-- The projection onto the second coordinate is a linear map -/
-- instance snd_linear : is_linear_map R (project_snd M N) := 
-- { add := λ x y, snd_additivity M N x y,
--   smul := λ r x, snd_smul R M N r x,
-- }

-- /-- The inclusion to the first coordinate is a linear map -/
-- instance include_fst_linear : is_linear_map R (include_fst M N) :=
-- { add := include_fst_add M N,
--   smul := include_fst_smul R M N}

-- /-- The inclusion to the second coordinate is a linear map -/
-- instance include_snd_linear : is_linear_map R (include_snd M N) :=
-- { add := include_snd_add M N,
--   smul := include_snd_smul R M N}

-- end direct_sum



/-- A module decomposes iff there is an idempotent endomorphism of M -/
lemma decomposes_iff_idempotent : decomposes R M ↔ ∃ (f : M →ₗ[R] M), f ∘ f = f :=
  begin
  apply iff.intro,
  intro,
  cases a with L h,
  cases h with N split,
  -- The composition of the projection and inclusion maps is a linear map M → M
  let comp := linear_map_.linear_composition R (direct_sum.include_fst L N) (direct_sum.project_fst L N),
  have comp_idem : comp ∘ comp = comp := begin funext, simp,
    show ((x.fst, (0:N)).fst, (0:N)) = (x.fst, (0:N)),
    simp,
    end,
  conv at comp {congr, skip, rw ← split, skip, rw ← split,},
  sorry,
  -- Now the converse direction
  intro,
  cases a with f f_idem,
  let ker := @map.kernel R M M _ _ _ _ _ f (linear_map.is_linear f),
  let im := @map.image R M M _ _ _ _ _ f (linear_map.is_linear f),
  -- Show that ker + im = M. The trick is to write m = m - f(m) + f(m)
  have sum_spans : ∀ (m : M), ∃ (x ∈ ker) (y ∈ im), m = x + y := begin
    intro m,
    let ker_elt := m - f m,
    have ker_elt_mem : ker_elt ∈ ker := begin
      simp,
      conv_lhs {congr, skip, congr, change (f ∘ f) m, rw f_idem,},
      simp,
      end,
    let im_elt := f m,
    have im_elt_mem : im_elt ∈ im := by {simp, existsi m, simp},
    existsi [ker_elt, ker_elt_mem, im_elt, im_elt_mem],
    show m = m - f m + f m,
    simp,
    end,
  -- Show that ker ∩ im = 0
  have zero_inter : ker.carrier ∩ im.carrier = ({0} : set M) := 
    begin 
    ext,
    apply iff.intro,
    -- First show that x ∈ LHS → x = 0
    intro hx,
    simp,
    have hx_im : x ∈ im := hx.right,
    have hx_ker : x ∈ ker := hx.left,
    simp at hx_im,
    simp at hx_ker,
    cases hx_im with m₁ hm₁,
    have im_mem_ker : f (f m₁) = f x := by rw hm₁,
    conv at im_mem_ker {to_lhs, change (f ∘ f) m₁, rw f_idem},
    rw hx_ker at im_mem_ker,
    rw hm₁ at im_mem_ker,
    exact im_mem_ker,
    -- Now show that x = 0 → x ∈ LHS
    simp,
    intro hx,
    split,
    show ∃ (m : M), f m = x, -- show that x ∈ im
    existsi (0 : M),
    rw hx,
    simp,
    show f x = 0, -- Show that x ∈ ker
    rw hx,
    simp,
    end,
  show ∃ (L N : submodule R M), M = (L × N),
  existsi [ker, im],
  rw decomposes_iff_sum,
  split,
  exact sum_spans,
  exact zero_inter,
  end