import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames

/-! # Cocycle Origin Scalar -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CocycleOriginScalar.Construction

noncomputable section

/-! The actual kernel cocycle at the zero point is the canonical
descent scalar between zero and the included kernel point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames.Construction

universe u

theorem pullbackLineKernelCocycle_one_scalar {S : Scheme.{u}} {A B : Over S}
    [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    {T : Over S} (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L e).value 1 z =
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf) e
        (1 : T ⟶ B).left (1 : T ⟶ A).left (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left
        (congrArg Over.Hom.left (MonObj.one_comp f))
        (congrArg Over.Hom.left (show (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) ≫ f = 1 by
          rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one])) :=
  Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar_congr (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf) e
    _ _ _ _ _ _ _ _ _ _ (congrArg Over.Hom.left (MonObj.one_comp f)) rfl
      (congrArg Over.Hom.left (one_mul _))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CocycleOriginScalar.Construction
