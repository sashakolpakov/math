import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.LocalSmoothness
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterEtaleBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ComplexNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.ComplexAffineDifferentialIdeal

/-! # Open Boundary Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenBoundaryTransport.Construction

noncomputable section

/-! Transport actual affine boundary charts to native affine opens of the ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def specOpenImage {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] : X.affineOpens :=
  ⟨j ''ᵁ ⊤, (isAffineOpen_top (Spec R)).image_of_isOpenImmersion j⟩

theorem specOpenImage_eq_opensRange {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] : (specOpenImage R j).1 = j.opensRange :=
  Scheme.Hom.image_top_eq_opensRange j

def specOpenSectionEquiv {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] : Γ(X, specOpenImage R j) ≃+* R :=
  (j.appIso ⊤).commRingCatIsoToRingEquiv.trans (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

theorem specOpenSectionEquiv_ideal {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] (J : X.IdealSheafData) (K : Ideal R)
    (h : J.comap j = QuotientKernel.Construction.affineQuotientKernel K) :
    J.ideal (specOpenImage R j) = K.comap (specOpenSectionEquiv R j).toRingHom := by
  let V : (Spec R).affineOpens := ⟨⊤, isAffineOpen_top (Spec R)⟩
  have he := congrArg (fun D : (Spec R).IdealSheafData => D.ideal V) h
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, QuotientKernel.Construction.affineQuotientKernel_idealTop] at he
  change (J.ideal (specOpenImage R j)).comap (j.appIso ⊤).inv.hom =
    K.comap (Scheme.ΓSpecIso R).hom.hom at he
  let e₀ : Γ(X, specOpenImage R j) ≃+* Γ(Spec R, ⊤) := (j.appIso ⊤).commRingCatIsoToRingEquiv
  let e₁ : Γ(Spec R, ⊤) ≃+* R := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have he' : (J.ideal (specOpenImage R j)).comap e₀.symm.toRingHom = K.comap e₁.toRingHom := he
  ext x
  change x ∈ J.ideal (specOpenImage R j) ↔ e₁ (e₀ x) ∈ K
  have hx := congrArg (fun A : Ideal Γ(Spec R, ⊤) => e₀ x ∈ A) he'
  change (e₀.symm (e₀ x) ∈ J.ideal (specOpenImage R j)) = (e₁ (e₀ x) ∈ K) at hx
  rw [e₀.symm_apply_apply] at hx
  exact Iff.of_eq hx

theorem specOpenSectionEquiv_equation {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] (J : X.IdealSheafData) (w : R)
    (h : J.comap j = QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w})) :
    J.ideal (specOpenImage R j) = Ideal.span {(specOpenSectionEquiv R j).symm w} := by
  rw [specOpenSectionEquiv_ideal R j J _ h]
  calc
    (Ideal.span {w}).comap (specOpenSectionEquiv R j).toRingHom =
        (Ideal.span {w}).map (specOpenSectionEquiv R j).symm.toRingHom :=
      (Ideal.map_symm (specOpenSectionEquiv R j) (I := Ideal.span {w})).symm
    _ = _ := by rw [Ideal.map_span, Set.image_singleton]; rfl

def specOpenSectionAlgEquiv {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (R : CommRingCat)
    [Algebra ℂ R] (j : Spec R ⟶ X) [IsOpenImmersion j]
    (hstructure : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) :
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (specOpenImage R j)
    Γ(X, specOpenImage R j) ≃ₐ[ℂ] R := by
  let : Algebra ℂ Γ(X, specOpenImage R j) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (specOpenImage R j)
  refine { __ := specOpenSectionEquiv R j, commutes' := ?_ }
  intro c
  have h := RingHom.congr_fun
    (ComplexNaturality.Construction.affineComplexScalars_appIso f j ⟨⊤, isAffineOpen_top (Spec R)⟩) c
  rw [hstructure, ComplexAffineDifferentialIdeal.Construction.affineComplexScalars_spec_top] at h
  change (j.appIso ⊤).hom.hom (ComplexNaturality.Construction.affineComplexScalars f (specOpenImage R j) c) =
    (Scheme.ΓSpecIso R).inv.hom (algebraMap ℂ R c) at h
  change (Scheme.ΓSpecIso R).hom.hom ((j.appIso ⊤).hom.hom
    (ComplexNaturality.Construction.affineComplexScalars f (specOpenImage R j) c)) = algebraMap ℂ R c
  rw [h]
  exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.apply_symm_apply _

theorem exists_native_affine_boundary_equations
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (R : CommRingCat) [Algebra ℂ R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (hstructure : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R)
    {ι : Type} (D : ι → X.IdealSheafData) (w : ι → R) (L : List (Finset ι))
    (hD : ∀ l, (D l).comap j = QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l}))
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ R w) (hfaces : Boundary.Schedule.Construction.BoundaryFacesCover w L) :
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (specOpenImage R j)
    ∃ v : ι → Γ(X, specOpenImage R j),
      (∀ l, (D l).ideal (specOpenImage R j) = Ideal.span {v l}) ∧
      LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of Γ(X, specOpenImage R j)) v ∧ Boundary.Schedule.Construction.BoundaryFacesCover v L := by
  let : Algebra ℂ Γ(X, specOpenImage R j) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (specOpenImage R j)
  let e := specOpenSectionAlgEquiv f R j hstructure
  let v : ι → Γ(X, specOpenImage R j) := fun l => e.symm (w l)
  refine ⟨v, ?_, ?_, hfaces.map e.symm.toRingHom⟩
  · intro l
    exact specOpenSectionEquiv_equation R j (D l) (w l) (hD l)
  · exact hboundary.etale_baseChange (S := .of Γ(X, specOpenImage R j)) e.symm.toAlgHom
      (RingHom.Etale.of_bijective e.symm.bijective)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenBoundaryTransport.Construction
