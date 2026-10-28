import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.FiberGenericPoint

/-! # Deformation Flat -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationFlat.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: flatness and surjectivity of the punctured deformation projection -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def puncturedLaurentCover : (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I).OpenCover :=
  Scheme.Cover.mkOfCovers X.AffineZariskiSite
    (fun U => Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))))
    (DeformationCharts.BundleCycles.puncturedLaurentChart I) (DeformationCharts.BundleCycles.puncturedLaurentChart_covers I)

instance puncturedDeformationProjection_flat : Flat (DeformationCharts.BundleCycles.puncturedDeformationProjection I) := by
  let : IsZariskiLocalAtSource @Flat.{0} :=
    @HasRingHomProperty.instIsZariskiLocalAtSource @Flat.{0} @RingHom.Flat.{0}
      Flat.instHasRingHomPropertyFlat
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat.{0}) (puncturedLaurentCover I)).mpr
  intro U
  change Flat (DeformationCharts.BundleCycles.puncturedLaurentChart I U ≫ DeformationCharts.BundleCycles.puncturedDeformationProjection I)
  exact (congrArg (fun f => Flat f) (DeformationCharts.BundleCycles.puncturedLaurentChart_toBase I U)).mpr
    (@Flat.comp _ _ _ (Laurent.FiberGenericPoint.BundleCycles.laurentProjection Γ(X, U.1)) U.2.fromSpec inferInstance inferInstance)

theorem puncturedDeformationProjection_surjective :
    Function.Surjective (DeformationCharts.BundleCycles.puncturedDeformationProjection I) := by
  intro x
  let U : X.AffineZariskiSite := (directedCover X).idx x
  obtain ⟨y, hy⟩ := (directedCover X).covers x
  have hx : x ∈ (U.1 : Set X) := hy ▸ y.property
  obtain ⟨p, hp⟩ := (congrArg (fun s : Set X => x ∈ s) U.2.range_fromSpec).mpr hx
  refine ⟨DeformationCharts.BundleCycles.puncturedLaurentChart I U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint Γ(X, U.1) p), ?_⟩
  have hc := congrArg (fun k => k (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint Γ(X, U.1) p))
    (DeformationCharts.BundleCycles.puncturedLaurentChart_toBase I U)
  exact hc.trans ((congrArg U.2.fromSpec (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint_projection Γ(X, U.1) p)).trans hp)

end

/-! # LineBundleCycles: a chart-independent generic point of each punctured deformation fiber -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem puncturedLaurentChart_prime_projection (U : X.AffineZariskiSite)
    (p : Spec (CommRingCat.of Γ(X, U.1))) :
    DeformationCharts.BundleCycles.puncturedDeformationProjection I (DeformationCharts.BundleCycles.puncturedLaurentChart I U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint Γ(X, U.1) p)) =
      U.2.fromSpec p :=
  (congrArg (fun k => k (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint Γ(X, U.1) p)) (DeformationCharts.BundleCycles.puncturedLaurentChart_toBase I U)).trans
    (congrArg U.2.fromSpec (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint_projection Γ(X, U.1) p))

theorem puncturedLaurentChart_prime_specializes (U : X.AffineZariskiSite)
    (p : Spec (CommRingCat.of Γ(X, U.1))) (y : Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I)
    (hy : DeformationCharts.BundleCycles.puncturedDeformationProjection I y = U.2.fromSpec p) :
    DeformationCharts.BundleCycles.puncturedLaurentChart I U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint Γ(X, U.1) p) ⤳ y := by
  have hyr : y ∈ Set.range (DeformationCharts.BundleCycles.puncturedLaurentChart I U) := by
    rw [DeformationCharts.BundleCycles.puncturedLaurentChart_range]
    change DeformationCharts.BundleCycles.puncturedDeformationProjection I y ∈ (U.1 : Set X)
    rw [hy, ← U.2.range_fromSpec]
    exact ⟨p, rfl⟩
  obtain ⟨P, rfl⟩ := hyr
  have hp : Laurent.FiberGenericPoint.BundleCycles.laurentProjection Γ(X, U.1) P = p := by
    apply U.2.fromSpec.isOpenEmbedding.injective
    exact (congrArg (fun k => k P) (DeformationCharts.BundleCycles.puncturedLaurentChart_toBase I U)).symm.trans hy
  exact (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint_specializes_fiber Γ(X, U.1) p P hp).map
    (DeformationCharts.BundleCycles.puncturedLaurentChart I U).continuous

theorem puncturedFiberGenericPoint_exists (x : X) :
    ∃ z : Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I, DeformationCharts.BundleCycles.puncturedDeformationProjection I z = x ∧
      ∀ y, DeformationCharts.BundleCycles.puncturedDeformationProjection I y = x → z ⤳ y := by
  obtain ⟨y, hy⟩ := puncturedDeformationProjection_surjective I x
  obtain ⟨U, P, hP⟩ := DeformationCharts.BundleCycles.puncturedLaurentChart_covers I y
  let p := Laurent.FiberGenericPoint.BundleCycles.laurentProjection Γ(X, U.1) P
  have hp : U.2.fromSpec p = x :=
    (congrArg (fun k => k P) (DeformationCharts.BundleCycles.puncturedLaurentChart_toBase I U)).symm.trans
      ((congrArg (DeformationCharts.BundleCycles.puncturedDeformationProjection I) hP).trans hy)
  refine ⟨DeformationCharts.BundleCycles.puncturedLaurentChart I U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint Γ(X, U.1) p),
    (puncturedLaurentChart_prime_projection I U p).trans hp, ?_⟩
  intro z hz
  exact puncturedLaurentChart_prime_specializes I U p z (hz.trans hp.symm)

def puncturedFiberGenericPoint (x : X) : Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I :=
  (puncturedFiberGenericPoint_exists I x).choose

theorem puncturedFiberGenericPoint_projection (x : X) :
    DeformationCharts.BundleCycles.puncturedDeformationProjection I (puncturedFiberGenericPoint I x) = x :=
  (puncturedFiberGenericPoint_exists I x).choose_spec.1

theorem puncturedFiberGenericPoint_specializes (x : X) (y : Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I)
    (hy : DeformationCharts.BundleCycles.puncturedDeformationProjection I y = x) : puncturedFiberGenericPoint I x ⤳ y :=
  (puncturedFiberGenericPoint_exists I x).choose_spec.2 y hy

theorem puncturedFiberGenericPoint_on_chart (U : X.AffineZariskiSite)
    (p : Spec (CommRingCat.of Γ(X, U.1))) :
    puncturedFiberGenericPoint I (U.2.fromSpec p) =
      DeformationCharts.BundleCycles.puncturedLaurentChart I U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint Γ(X, U.1) p) := by
  exact ((puncturedFiberGenericPoint_specializes I _ _
    (puncturedLaurentChart_prime_projection I U p)).antisymm
      (puncturedLaurentChart_prime_specializes I U p _
        (puncturedFiberGenericPoint_projection I _))).eq

theorem puncturedFiberGenericPoint_injective : Function.Injective (puncturedFiberGenericPoint I) :=
  Function.LeftInverse.injective (puncturedFiberGenericPoint_projection I)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationFlat.BundleCycles
