import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenBoundaryTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv

/-! # Intrinsic Affine Normal Frames -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicAffineNormalFrames.Construction

noncomputable section

/-! Transfer actual dual normal frames to the native rings of affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_native_affine_normal_frame
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I H : X.IdealSheafData)
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (p : PrimeSpectrum R)
    {ι : Type} [DecidableEq ι] (v : ι → R) (D : ι → Derivation ℂ R R)
    (hD : ∀ i l, D i (v l) = if i = l then 1 else 0) (l : ι)
    (hI : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span (Set.range v)))
    (hH : H.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v l})) :
    ∃ U : X.affineOpens, j p ∈ U.1 ∧
      letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
      ∃ (g : ι → I.ideal U) (E : ι → Derivation ℂ Γ(X, U) Γ(X, U)),
        (∀ i l, E i (g l).val = if i = l then 1 else 0) ∧
        Ideal.span (Set.range (fun i => (g i).val)) = I.ideal U ∧
        H.ideal U = Ideal.span {(g l).val} := by
  let U := Affine.OpenBoundaryTransport.Construction.specOpenImage R j
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let e := Affine.OpenBoundaryTransport.Construction.specOpenSectionAlgEquiv f R j hj
  let w (i : ι) := e.symm (v i)
  have hgen : I.ideal U = Ideal.span (Set.range w) := by
    rw [Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_ideal R j I _ hI]
    change (Ideal.span (Set.range v)).comap e.toRingEquiv = _
    rw [← Ideal.map_symm e.toRingEquiv, Ideal.map_span, ← Set.range_comp]
    rfl
  let g : ι → I.ideal U := fun i => ⟨w i, hgen.symm ▸ Ideal.subset_span ⟨i, rfl⟩⟩
  let E (i : ι) := Relative.DifferentialEquiv.Construction.transportRelativeDerivation e.symm (D i)
  refine ⟨U, ?_, g, E, ?_, hgen.symm, ?_⟩
  · change j p ∈ (Affine.OpenBoundaryTransport.Construction.specOpenImage R j).1
    rw [Affine.OpenBoundaryTransport.Construction.specOpenImage_eq_opensRange]
    exact ⟨p, rfl⟩
  · intro i t
    change Relative.DifferentialEquiv.Construction.transportRelativeDerivation e.symm (D i) (e.symm (v t)) = _
    rw [Relative.DifferentialEquiv.Construction.transportRelativeDerivation_map, hD]
    split_ifs <;> simp
  · exact Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_equation R j H (v l) hH

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicAffineNormalFrames.Construction
