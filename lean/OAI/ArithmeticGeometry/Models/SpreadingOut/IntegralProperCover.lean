import OAI.ArithmeticGeometry.Models.SpreadingOut.ChowCriterion
import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperProducts
import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteAffineCover
import OAI.ArithmeticGeometry.Models.SpreadingOut.AffineProjectiveChart
import OAI.ArithmeticGeometry.Models.SpreadingOut.Cover

/-! # Integral Proper Cover -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.IntegralProperCover.Construction

noncomputable section

/-! A proper covering model for an integral proper scheme, constructed from
finitely many affine charts and the closure of their combined graph. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.NumberField

universe u

theorem integral_proper_scheme_has_integral_cover
    (K : Type u) [Field K] [NumberField K]
    (X : Over (Spec (.of K))) [IsIntegral X.left] [IsProper X.hom] :
    ∃ (Z : Over (Spec (.of K))) (f : Z ⟶ X), Surjective f.left ∧
      ∃ P : Over (Spec (.of (𝓞 K))), IsProper P.hom ∧
        Nonempty ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)))).obj P ≅ Z) := by
  classical
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := ⟨⟩
  obtain ⟨ι, hι, V, hV, hcover⟩ := FiniteAffineCover.Construction.finite_nonempty_affine_open_cover X.left
  have := hι
  have (i : ι) : IsAffine (OpenOver.Construction.overOpen X (V i)).left := (hV i).1
  have (i : ι) : LocallyOfFiniteType (OpenOver.Construction.overOpen X (V i)).hom := by
    change LocallyOfFiniteType ((V i).ι ≫ X.hom)
    infer_instance
  choose n A e he using fun i ↦
    AffineProjectiveChart.Construction.affine_has_closed_generic_projective_chart (𝓞 K) K (OpenOver.Construction.overOpen X (V i))
  let g := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K))
  let P : ι → Over (Spec (.of (𝓞 K))) := fun i ↦ ProjectiveEmbedding.Construction.projectiveModel (𝓞 K) (n i)
  obtain ⟨M⟩ := ProperProducts.Construction.proper_family_has_product P (fun i ↦ inferInstance)
  let N := M.baseChange g
  have : IsProper M.obj.hom := M.proper
  have : IsProper N.obj.hom := N.proper
  let Q : ι → Over (Spec (.of K)) := fun i ↦ (Over.pullback g).obj (P i)
  have hQ (i : ι) : IsSeparated (Q i).hom := by
    change IsSeparated (pullback.snd (P i).hom g)
    have : IsProper (P i).hom := inferInstanceAs (IsProper (ProjectiveEmbedding.Construction.projectiveModel (𝓞 K) (n i)).hom)
    infer_instance
  obtain ⟨T, hT, hTV⟩ := FiniteAffineCover.Construction.common_dense_open X.left V (fun i ↦ (hV i).2)
  let W := OpenOver.Construction.overOpen X T
  let j := OpenOver.Construction.overOpenInclusion X T
  have : IsDominant j.left := Opens.isDominant_ι hT
  have hTc : IsCompact (T : Set X.left) := NoetherianSpace.isCompact _
  have : CompactSpace W.left := isCompact_iff_compactSpace.mp hTc
  let k : ∀ i, W ⟶ OpenOver.Construction.overOpen X (V i) := fun i ↦
    Over.homMk (X.left.homOfLE (hTV i)) (by
      change X.left.homOfLE (hTV i) ≫ ((V i).ι ≫ X.hom) = T.ι ≫ X.hom
      rw [← Category.assoc, Scheme.homOfLE_ι])
  have hk (i : ι) : j = k i ≫ OpenOver.Construction.overOpenInclusion X (V i) := by
    apply Over.OverMorphism.ext
    exact (Scheme.homOfLE_ι X.left (hTV i)).symm
  let a : W ⟶ N.obj := N.lift W
    (fun i ↦ k i ≫ e i ≫ OpenOver.Construction.overOpenInclusion (Q i) (A i))
  have ha (i : ι) : a ≫ N.projection i =
      k i ≫ e i ≫ OpenOver.Construction.overOpenInclusion (Q i) (A i) := N.lift_projection W _ i
  have : IsLocallyNoetherian N.obj.left := LocallyOfFiniteType.isLocallyNoetherian N.obj.hom
  have : IsLocallyNoetherian (pullback X.hom N.obj.hom) := inferInstance
  have : QuasiCompact (GraphClosure.Construction.rationalGraph j a) := inferInstance
  let Z := GraphClosure.Construction.graphClosure j a
  let f := GraphClosure.Construction.graphClosureToX j a
  let i : Z ⟶ (Over.pullback g).obj M.obj := GraphClosure.Construction.graphClosureToP j a
  have hf : Surjective f.left := GraphClosure.Construction.graphClosureToX_surjective j a
  have : IsClosedImmersion i.left :=
    ChowCriterion.Construction.graphClosureToP_closed_of_chart_cover j a Q hQ N.projection V hcover A k e he hk ha
  have : IsPreimmersion g := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 K))
  obtain ⟨P₀, hP₀, hgeneric⟩ := ProperAmbient.Construction.closed_generic_subscheme_has_proper_model g M.obj Z i
  exact ⟨Z, f, hf, P₀, hP₀, hgeneric⟩

/-- The first SpreadingOut conclusion for an integral smooth proper scheme. -/
theorem integral_smooth_proper_arithmetic_model
    (K : Type u) [Field K] [NumberField K]
    (X : Over (Spec (.of K))) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom] :
    ∃ (B : Base.Construction.ArithmeticOpen K) (M : Over B.U.toScheme),
      Smooth M.hom ∧ IsProper M.hom ∧
      Nonempty ((Over.pullback B.generic).obj M ≅ X) := by
  obtain ⟨Z, f, hf, P, hP, ⟨e⟩⟩ := integral_proper_scheme_has_integral_cover K X
  have := hf
  have := hP
  exact Cover.Construction.arithmetic_model_of_proper_integral_cover f P e

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.IntegralProperCover.Construction
