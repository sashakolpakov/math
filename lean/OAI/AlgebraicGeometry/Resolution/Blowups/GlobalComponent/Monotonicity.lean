import OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterMonotonicity
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelOrderEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.CenterRestriction

/-! # Monotonicity -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent

noncomputable section

/-! Monotonicity of the actual global component center, independently of its chosen atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_mono {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J L : X.IdealSheafData} {n : ℕ}
    (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (B : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f L n) (h : J ≤ L) :
    A.center ≤ B.center := by
  apply Center.Construction.idealSheaf_le_of_native_affine_cover A.nativeOpens A.nativeOpens_cover
  intro i
  obtain ⟨K, hK⟩ := Affine.KernelOrderEquiv.Construction.exists_affineQuotientKernel (L.comap (A.map i))
  have hJK : A.ideals i ≤ K := by
    apply (Affine.KernelOrderEquiv.Construction.affineQuotientKernel_le_iff _ _).mp
    rw [← A.ideal_eq i, hK]
    exact Scheme.IdealSheafData.comap_mono (A.map i) h
  let C := (A.choice i).enlarge hJK
  have hB := B.center_restrict_any (A.rings i) (A.map i) (A.ground i) K hK.symm C
  rw [A.center_ideal i, Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_ideal (A.rings i) (A.map i) B.center C.center hB]
  exact Ideal.comap_mono ((A.choice i).center_le_enlarge hJK)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent
