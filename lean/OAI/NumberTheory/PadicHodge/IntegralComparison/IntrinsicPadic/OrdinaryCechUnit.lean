import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.EtaleCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution

/-! # Ordinary Cech Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryCechUnit.IntrinsicOrdinary

noncomputable section

/-! The original integral coordinate cover computes the sheafified de
Rham complex in every degree. Its full ordinary cohomology is finite. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

theorem forms (q : ℕ) (t : Fin (q+1) → GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) (n : ℕ) :
    IsIso (((AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit ℤ_[p] X).f n).app (op (∏ᶜ (U ∘ t)))) := by
  have hI : IsAffineOpen (∏ᶜ (U ∘ t)) := by
    rw [AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.product_iInf]
    exact IsAffineOpen.iInf (fun j => GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X (t j))
  let I : X.left.affineOpens := ⟨∏ᶜ (U ∘ t), hI⟩
  have hi : I.val ≤ U (t 0) := leOfHom (Pi.π (U ∘ t) 0)
  let σ := GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateIndex ℤ_[p] X (t 0)
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Algebra (MvPolynomial σ ℤ_[p]) (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring ℤ_[p] X I.val) :=
    GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.padicPolynomialAlgebra p X I (t 0) hi
  let : IsScalarTower ℤ_[p] (MvPolynomial σ ℤ_[p])
      (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring ℤ_[p] X I.val) :=
    GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.padicTower p X I (t 0) hi
  let : Algebra.Etale (MvPolynomial σ ℤ_[p])
      (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring ℤ_[p] X I.val) :=
    GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.padicEtale p X I (t 0) hi
  exact AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit.forms ℤ_[p] X I.val I.property σ n

def bicomplex : HomologicalComplex₂ (ModuleCat.{0} ℤ_[p]) (.up ℕ) (.up ℕ) :=
  ((NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).obj
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℤ_[p] X)

def map : bicomplex p X ⟶ IntrinsicDeRham.CechComplex.Intrinsic.bicomplex ℤ_[p] X U :=
  ((NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).map
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit ℤ_[p] X)

theorem row_isIso (n : ℕ) : IsIso ((IntrinsicOrdinary.map p X).f n) :=
  GeometricComparison.Cech.TermwiseIso.CechTermwiseIso.isIso N ((AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit ℤ_[p] X).f n)
    (fun q t => forms p X q t n)

def iso : bicomplex p X ≅ IntrinsicDeRham.CechComplex.Intrinsic.bicomplex ℤ_[p] X U := by
  let (n : ℕ) : IsIso ((IntrinsicOrdinary.map p X).f n) := row_isIso p X n
  let : IsIso (IntrinsicOrdinary.map p X) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (IntrinsicOrdinary.map p X)

def totalIso : (bicomplex p X).total (.up ℕ) ≅ IntrinsicDeRham.CechComplex.Intrinsic.total ℤ_[p] X U :=
  HomologicalComplex₂.total.mapIso (iso p X) (.up ℕ)

theorem finite (i : ℕ) : Module.Finite ℤ_[p] (((bicomplex p X).total (.up ℕ)).homology i) := by
  let : Module.Finite ℤ_[p] ((IntrinsicDeRham.CechComplex.Intrinsic.total ℤ_[p] X U).homology i) :=
    IntrinsicDeRham.CechFiniteness.Intrinsic.finite ℤ_[p] X U
      (TopologicalSpace.IsOpenCover.mk (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X))
      (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X) i
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (totalIso p X) i).symm.toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryCechUnit.IntrinsicOrdinary
