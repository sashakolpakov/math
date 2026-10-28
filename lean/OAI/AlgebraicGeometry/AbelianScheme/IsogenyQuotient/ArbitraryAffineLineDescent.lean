import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.PresentationFlatDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineSchemeEffectivity

/-! # Arbitrary Affine Line Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArbitraryAffineLineDescent.Construction

noncomputable section

/-! The actual ordinary invariant sheaf is a line bundle after
faithfully flat descent over arbitrary affine bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.ModuleCat
open TensorProduct

universe u

theorem arbitrary_descendedModule_invertible
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat) (D : Picard.PoincareBundle.Affine.Descent.ModuleDatum f)
    [Module.Invertible S D.A] : Module.Invertible R (Picard.PoincareBundle.Affine.Descent.descendedModule f hf D) := by
  let : Algebra R S := f.toAlgebra
  have : Module.FaithfullyFlat R S := hf
  have : Module.Invertible S (S ⊗[R] Picard.PoincareBundle.Affine.Descent.descendedModule f hf D) :=
    Module.Invertible.congr (Picard.PoincareBundle.Affine.Descent.baseChangeIso f hf D).symm.toLinearEquiv
  exact Finite.PresentationFlatDescent.Construction.module_invertible_of_faithfullyFlat_baseChange R S _

theorem arbitrary_geometricBaseModule_invertible
    {R S : CommRingCat.{u}} (f : R ⟶ S) (D : Picard.PoincareBundle.Geometric.CocycleDescent.RingMapDatum f)
    (hf : f.hom.FaithfullyFlat) : Module.Invertible R (Picard.PoincareBundle.Geometric.CechRecovery.baseModule f D hf) := by
  have : Module.Invertible S
      (Picard.PoincareBundle.CocycleEffectiveDescent.moduleDatum f.hom (Picard.PoincareBundle.Geometric.CechRecovery.sectionModule f D)
        (Picard.PoincareBundle.Geometric.CechRecovery.moduleCech f D)).A :=
    Picard.PoincareBundle.Affine.Classification.globalSections_invertible (Picard.PoincareBundle.Geometric.CechRecovery.originalLine f D)
  exact arbitrary_descendedModule_invertible f.hom hf
    (Picard.PoincareBundle.CocycleEffectiveDescent.moduleDatum f.hom (Picard.PoincareBundle.Geometric.CechRecovery.sectionModule f D)
      (Picard.PoincareBundle.Geometric.CechRecovery.moduleCech f D))

theorem arbitrary_affineCechInvariant_isLine
    {R S : CommRingCat.{u}} (f : R ⟶ S) (D : Picard.PoincareBundle.Geometric.CocycleDescent.RingMapDatum f)
    (hf : f.hom.FaithfullyFlat) : Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.Affine.CechInvariantMaps.invariant f D) := by
  have := arbitrary_geometricBaseModule_invertible f D hf
  exact (Picard.PoincareBundle.TildePullback.isLine_tilde_of_invertible (Picard.PoincareBundle.Geometric.CechRecovery.baseModule f D hf)).of_iso
    (Picard.PoincareBundle.Affine.CechEffectivity.invariantIso f D hf)

theorem arbitrary_ordinaryAffineInvariant_isLine
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => Spec.map f))
    (hline : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit)) (hf : f.hom.FaithfullyFlat) :
    Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf (Spec.map f) D) :=
  (arbitrary_affineCechInvariant_isLine f
    (Picard.PoincareBundle.Ordinary.AffineDescent.ringMapGeometricDatum f D hline) hf).of_iso
      (Picard.PoincareBundle.Ordinary.AffineEffectivity.invariantIso f D hline)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArbitraryAffineLineDescent.Construction
