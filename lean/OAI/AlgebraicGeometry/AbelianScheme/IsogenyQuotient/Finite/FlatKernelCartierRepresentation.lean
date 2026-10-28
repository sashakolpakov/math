import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGeometry

/-! # Flat Kernel Cartier Representation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatKernelCartierRepresentation.Construction

noncomputable section

/-! The actual finite-flat kernel has its Cartier character
representative by the proved CartierDuality construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGeometry.Construction OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion.Construction

universe u

def finiteFlatKernelCartierRepresentation {S : Scheme.{u}} {X A : Over S}
    [GrpObj X] [IsCommMonObj X] [GrpObj A] (f : X ⟶ A) [IsMonHom f]
    [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left] :
    CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) := by
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := hK.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := hK.2.1
  have : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := hK.2.2
  exact CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatKernelCartierRepresentation.Construction
