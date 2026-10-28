import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierChartBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealSubopenEquation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PullbackAffineKernel

/-! # Cartier Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChange.BundleCycles

noncomputable section

/-! A relative effective Cartier divisor that is flat over its
base remains an effective Cartier divisor after every base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem relativeCartier_regularPrincipalImageIdeals_baseChange
    {S S' X X' Z Z' : Scheme.{0}}
    (p : X ⟶ S) (p' : X' ⟶ S') (f : X' ⟶ X) (h : S' ⟶ S)
    (hp : IsPullback f p' p h)
    (i : Z ⟶ X) [IsClosedImmersion i] [Flat (i ≫ p)]
    (j : Z' ⟶ X') (g : Z' ⟶ Z) (hj : IsPullback j g f i)
    (hi : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals i) : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals j := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p (f x) ∈ (⊤ : S.Opens) from trivial)
  let L := Cartier.IdealBundle.Cycles.cartierIdealLineBundle i hi
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ L.trivializingOpen (f x) ⊓ p ⁻¹ᵁ U from ⟨L.mem_trivializingOpen _, hxU⟩)
  have hxU' : p' x ∈ h ⁻¹ᵁ U := by
    change h (p' x) ∈ U
    have he : p (f x) = h (p' x) := congrArg (fun k => k x) hp.w
    rw [← he]
    exact hxU
  obtain ⟨U', hU', hxU', hU'U⟩ := exists_isAffineOpen_mem_and_subset hxU'
  let W : X'.Opens := f ⁻¹ᵁ V ⊓ p' ⁻¹ᵁ U'
  have hWAffine : IsAffineOpen W := by
    let : IsAffine U.toScheme := hU
    let : IsAffine V.toScheme := hV
    let : IsAffine U'.toScheme := hU'
    exact IsAffine.of_isIso
      (Scheme.Hom.isPullback_resLE hp hU'U (hVU.trans inf_le_right) rfl).isoPullback.hom
  let t := LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) (f x) V
    (hVU.trans inf_le_left)
  have ht : IsRegular t := Cartier.IdealSubopenEquation.BundleCycles.cartierIdealSubopenEquation_regular i hi (f x) V (hVU.trans inf_le_left)
  have hk : RingHom.ker (i.app V).hom = Ideal.span {t} :=
    Cartier.IdealSubopenEquation.BundleCycles.cartierIdealSubopenEquation_kernel i hi (f x) V (hVU.trans inf_le_left)
  refine ⟨⟨W, hWAffine⟩, ⟨hxV, hxU'⟩, f.appLE V W inf_le_left t, ?_, ?_⟩
  · exact CartierChartBaseChange.BundleCycles.relativeCartierChart_pullback_regular p p' f h hp i
      ⟨U, hU⟩ ⟨V, hV⟩ ⟨U', hU'⟩ (hVU.trans inf_le_right) hU'U t ht hk
  · rw [Closed.PullbackAffineKernel.BundleCycles.closedPullback_affineChart_kernel i j f g hj ⟨V, hV⟩ ⟨W, hWAffine⟩ inf_le_left,
      hk, Ideal.map_span, Set.image_singleton]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChange.BundleCycles
