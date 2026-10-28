import OAI.ArithmeticGeometry.Models.SpreadingOut.IntegralProperCover
import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothComponents

/-! # Smooth Proper Model -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothProperModel.Construction

noncomputable section

/-! Smooth proper arithmetic models, including disconnected schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.NumberField

universe u

theorem smooth_proper_scheme_has_integral_cover
    (K : Type u) [Field K] [NumberField K]
    (X : Over (Spec (.of K))) [Smooth X.hom] [IsProper X.hom] :
    ∃ (Z : Over (Spec (.of K))) (f : Z ⟶ X), Surjective f.left ∧
      ∃ P : Over (Spec (.of (𝓞 K))), IsProper P.hom ∧
        Nonempty ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)))).obj P ≅ Z) := by
  classical
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := ⟨⟩
  let ι := irreducibleComponents X.left
  have : Finite ι := finite_irreducibleComponents_of_isNoetherian.to_subtype
  let V : ι → X.left.Opens := SmoothComponents.Construction.smoothComponentOpen X.hom
  let C : ι → Over (Spec (.of K)) := fun i ↦ OpenOver.Construction.overOpen X (V i)
  have hC (i : ι) : IsIntegral (C i).left := SmoothComponents.Construction.smoothComponentOpen_integral X.hom i
  have hCP (i : ι) : IsProper (C i).hom :=
    (SmoothComponents.Construction.smoothComponentOpen_smooth_proper X.hom i).2
  choose Z f hf P hP e using fun i ↦ IntegralProperCover.Construction.integral_proper_scheme_has_integral_cover K (C i)
  let a : ∀ i, Z i ⟶ X := fun i ↦ f i ≫ OpenOver.Construction.overOpenInclusion X (V i)
  let F : ProperCoproducts.Construction.overSigma Z ⟶ X := ProperCoproducts.Construction.overSigmaDesc a
  have hF : Surjective F.left := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⨆ i, V i := by rw [SmoothComponents.Construction.smoothComponentOpen_cover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨z, hz⟩ := (hf i).surj ⟨x, hi⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, z, ?_⟩
    change (V i).ι ((f i).left z) = x
    rw [hz]
    rfl
  have hPS : IsProper (ProperCoproducts.Construction.overSigma P).hom :=
    ProperCoproducts.Construction.proper_finite_sigma_desc (𝓞 K) (fun i ↦ (P i).hom) hP
  let g := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K))
  exact ⟨ProperCoproducts.Construction.overSigma Z, F, hF, ProperCoproducts.Construction.overSigma P, hPS,
    ⟨ProperCoproducts.Construction.overSigmaBaseChangeIso g P ≪≫ ProperCoproducts.Construction.overSigmaIso (fun i ↦ (e i).some)⟩⟩

/-- Every smooth proper scheme over a number field extends over a cofinite
open of the spectrum of its ring of integers. -/
theorem smooth_proper_model_outside_finitely_many_primes
    (K : Type u) [Field K] [NumberField K]
    (X : Over (Base.Construction.fieldBase K)) [Smooth X.hom] [IsProper X.hom] :
    ∃ (B : Base.Construction.ArithmeticOpen K) (M : Over B.U.toScheme),
      Smooth M.hom ∧ IsProper M.hom ∧
      Nonempty ((Over.pullback B.generic).obj M ≅ X) := by
  obtain ⟨Z, f, hf, P, hP, ⟨e⟩⟩ := smooth_proper_scheme_has_integral_cover K X
  have := hf
  have := hP
  exact Cover.Construction.arithmetic_model_of_proper_integral_cover f P e

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothProperModel.Construction
