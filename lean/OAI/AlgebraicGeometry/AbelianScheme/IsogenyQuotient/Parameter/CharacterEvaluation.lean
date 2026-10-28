import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterSection
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation

/-! # Character Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEvaluation

noncomputable section

/-! Evaluation of the constructed internal-Hom section retains the
original character's regular unit at the identity parameter test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (Q : Over S)
  (χ : ∀ U : Over Q.left, (U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) →* Γ(U.left, ⊤)ˣ)
  (hχ : ∀ {U V : Over Q.left} (a : V ⟶ U) (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)),
    Units.map a.left.appTop.hom (χ U z) = χ V (a ≫ z))

theorem parameterCharacterSection_unit_value (z : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom Q (CartierDuality.Evaluation.Construction.CharacterEvaluation.value (CharacterSection.Construction.parameterCharacterSection f Q χ hχ) z) =
      χ (SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (𝟙 Q))) (SliceKernelPoints.Construction.parameterSliceKernelPoint Q f (Over.mk (𝟙 Q)) z) :=
  (MultiplicativeUnitEquiv.Construction.multiplicativeGroupUnitEquiv Q).apply_symm_apply _

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEvaluation
