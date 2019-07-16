-- Representation theory of finite groups. In particular, Maschke's theorem 
-- and character theory

import representation
import homological_algebra
import data.set.finite

open group_representation -- Potentially dangerous to open a namespace, however I will exclusively do 
-- group theory here, because Maschke's theorem fails for monoids. 
open direct_sum

variables (G K V : Type)
variables [group G] [discrete_field K] [add_comm_group V] [vector_space K V] [group_representation G K V]

-- These three lines give a proof that G is a finite group
def group_as_set : set G := {g | g = g}
lemma mem_group : ∀ (g:G), g ∈ group_as_set G := λ g, show g = g, from eq.refl g
variable G_is_finite : finset (group_as_set G)

/-- Maschke's theorem implies that an indecomposable representation is in fact irreducible.
    In fact, the precise statement is that if we have a subrepresentation of M, then M
    decomposes. -/
theorem subrepresentation_has_complement (U : subspace K V) : is_subrepresentation G U → 
    ∃ (W : submodule K V) [is_subrepresentation G W], V = (U × W) := 
begin
intro sub_rep,


sorry,
end

------ playground
variables (U : submodule K V) [is_subrepresentation G U]
#check subrepresentation_has_complement G K V U _