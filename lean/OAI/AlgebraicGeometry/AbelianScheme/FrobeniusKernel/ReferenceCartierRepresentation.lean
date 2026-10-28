import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualBaseChangeComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterLines

/-! # Reference Cartier Representation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceCartierRepresentation

noncomputable section

/-! The Cartier character-line point agrees in the two native
presentations of the original HilbertConstruction pulled-back dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

attribute [local instance] BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters

variable {S S' : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (s : S' ⟶ S)
variable (f : (Over.pullback s).obj A.scheme ⟶ (Over.pullback s).obj A.scheme) [hfGroup : IsMonHom f]
variable [hAffine : IsAffineHom f.left] [hFlat : Flat f.left] [hSurj : Surjective f.left]
variable [hPresent : LocallyOfFinitePresentation f.left]
variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

def nativeCartierPullbackMap : C.dual.X ⟶ (Over.pullback s).obj D.abelian.scheme :=
  @CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard S' ((Over.pullback s).obj A.scheme) ((Over.pullback s).obj A.scheme)
      (BaseChange.Construction.pulledBackGroup s A.scheme) (BaseChange.Construction.pulledBackGroup s A.scheme) f hfGroup hAffine hFlat hSurj hPresent
      (DualBaseChangeComparison.Construction.nativePullbackDualPicardData D s) C

def originalCartierPullbackMap : C.dual.X ⟶ (Over.pullback s).obj D.abelian.scheme :=
  @CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard S' ((Over.pullback s).obj A.scheme) ((Over.pullback s).obj A.scheme)
        (BaseChange.Construction.pulledBackGroup s A.scheme) (BaseChange.Construction.pulledBackGroup s A.scheme) f hfGroup hAffine hFlat hSurj hPresent
        (DualBaseChangeComparison.Construction.originalPullbackDualPicardData D s) C

theorem originalCartierRepresentation_baseChange :
    nativeCartierPullbackMap D s f C = originalCartierPullbackMap D s f C := by
  unfold nativeCartierPullbackMap originalCartierPullbackMap CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint
  exact DualBaseChangeComparison.Construction.nativeDualPicardPoint_ofBundled_pullback D s C.dual.X _

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceCartierRepresentation
