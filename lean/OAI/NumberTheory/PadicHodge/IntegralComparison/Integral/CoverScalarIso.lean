import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechScalarCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover

/-! # Cover Scalar Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CoverScalarIso

noncomputable section

/-! The original finite integral étale cover gives an isomorphism for
the actual native scalar comparison in every de Rham degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens R X

local instance schemeSeparated : X.left.IsSeparated := by
  constructor
  rw [← terminal.comp_from X.hom]
  infer_instance

theorem component_isIso (q : ℕ) (t : Fin (q+1) → GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index R X)
    (n : ℕ) : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.component R S X Y f hp.w (∏ᶜ (U ∘ t)) n) := by
  have hI : IsAffineOpen (∏ᶜ (U ∘ t)) :=
    AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine R X) q t
  let I : X.left.affineOpens := ⟨∏ᶜ (U ∘ t), hI⟩
  let i := t 0
  have hi : I.val ≤ GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens R X i := leOfHom (Pi.π (U ∘ t) 0)
  let σ := GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateIndex R X i
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Algebra R Γ(X.left, I.val) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X I.val
  let : Algebra (MvPolynomial σ R) Γ(X.left, I.val) :=
    @AffineOpen.EtaleCoordinates.polynomialAlgebra R inferInstance X I.val I.property
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateRing R X i) inferInstance
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap R X i) (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap_open R X i) hi
      σ (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.polynomialAlgebra R X i)
  let : IsScalarTower R (MvPolynomial σ R) Γ(X.left, I.val) :=
    @AffineOpen.EtaleCoordinates.tower R inferInstance X I.val I.property
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateRing R X i) inferInstance
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap R X i) (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap_open R X i) hi
      σ (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.polynomialAlgebra R X i)
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateAlgebra R X i) (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateTower R X i)
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap_over R X i)
  let : Algebra.Etale (MvPolynomial σ R) Γ(X.left, I.val) :=
    @AffineOpen.EtaleCoordinates.etale R inferInstance X I.val I.property
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateRing R X i) inferInstance
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap R X i) (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap_open R X i) hi
      σ (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.polynomialAlgebra R X i)
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateEtale R X i)
  exact AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.component_isIso R S X Y f hp.w I.val σ hp I.property n

theorem row_isIso (n : ℕ) : IsIso ((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w).f n) :=
  GeometricComparison.Cech.TermwiseIso.CechTermwiseIso.isIso (FormalCoproduct.mk (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index R X) U).cech
    (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.map R S X Y f hp.w n)
    (fun q t => component_isIso R S X Y f hp q t n)

theorem projection_isIso : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map R S X Y f hp.w U) := by
  let (n : ℕ) : IsIso ((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w).f n) :=
    row_isIso R S X Y f hp n
  let : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w) :=
    HomologicalComplex.Hom.isIso_of_components _
  dsimp only [AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map]
  infer_instance

theorem scalarMap_isIso : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.scalarMap R S X Y f hp.w U) := by
  let := projection_isIso R S X Y f hp
  change IsIso ((AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U)).inv ≫
      (HomologicalComplex₂.totalFunctor (ModuleCat S) (.up ℕ) (.up ℕ) (.up ℕ)).map
        (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map R S X Y f hp.w U))
  infer_instance

theorem homologyMap_isIso (n : ℕ) :
    IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f hp.w U n) := by
  let := scalarMap_isIso R S X Y f hp
  dsimp only [AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CoverScalarIso
