import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketChange

/-! # Change Representation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.ChangeRepresentation.Construction

noncomputable section

/-! Infinitesimal changes of basis on bilinear operations form a
representation of the commutator algebra of endomorphisms. -/

variable {k L : Type*} [Field k] [AddCommGroup L] [Module k L]

def bilinearChangeInfinitesimal (A : L →ₗ[k] L) :
    (L →ₗ[k] L →ₗ[k] L) →ₗ[k] (L →ₗ[k] L →ₗ[k] L) where
  toFun B := B.compr₂ A - B.compl₁₂ A LinearMap.id - B.compl₁₂ LinearMap.id A
  map_add' B C := by
    ext x y
    change A ((B + C) x y) - (B + C) (A x) y - (B + C) x (A y) = _
    simp only [LinearMap.add_apply, map_add, LinearMap.sub_apply,
      LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply]
    abel
  map_smul' c B := by
    ext x y
    change A ((c • B) x y) - (c • B) (A x) y - (c • B) x (A y) = _
    simp only [LinearMap.smul_apply, map_smul, LinearMap.sub_apply,
      LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply, smul_sub, RingHom.id_apply]

theorem bilinearChangeInfinitesimal_apply (A : L →ₗ[k] L) (B : L →ₗ[k] L →ₗ[k] L) (x y : L) :
    bilinearChangeInfinitesimal A B x y = A (B x y) - B (A x) y - B x (A y) := rfl

theorem bilinearChangeInfinitesimal_commutator (A C : L →ₗ[k] L) :
    bilinearChangeInfinitesimal (A * C - C * A) =
      bilinearChangeInfinitesimal A * bilinearChangeInfinitesimal C -
        bilinearChangeInfinitesimal C * bilinearChangeInfinitesimal A := by
  ext B x y
  simp only [bilinearChangeInfinitesimal_apply, LinearMap.sub_apply, Module.End.mul_apply,
    map_sub, LinearMap.sub_apply]
  abel

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.ChangeRepresentation.Construction
