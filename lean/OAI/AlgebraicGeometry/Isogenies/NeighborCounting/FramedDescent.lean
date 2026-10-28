import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FunctionDescent

/-! # Framed Descent -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent

noncomputable section

/-! Effective descent of line-bundle morphisms in actual local frames,
deduced from the proved regular-function descent theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FunctionDescent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}
variable (eM : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) (eN : N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y)

include eM eN in
theorem framedPullback_injective [Epi f] :
    Function.Injective (fun q : M ⟶ N ↦ (Scheme.Modules.pullback f).map q) := by
  intro q q' h
  apply (FramedHom.framedHomEquiv eM eN).symm.injective
  change FramedHom.framedCoefficient eM eN q = FramedHom.framedCoefficient eM eN q'
  apply FunctionDescent.appTop_injective_of_epi f
  rw [← FramedHom.framedCoefficient_pullback, ← FramedHom.framedCoefficient_pullback]
  exact congrArg (FramedHom.framedCoefficient (FramedHom.pullbackFrame f eM) (FramedHom.pullbackFrame f eN)) h

/-- Compatibility uses actual pullbacks on every equal-image pair of
test schemes, retaining nilpotent directions. -/
def CompatibleHom
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) : Prop :=
  ∀ {T : Scheme.{u}} (x y : T ⟶ X) (p : T ⟶ Y) (hx : x ≫ f = p) (hy : y ≫ f = p),
    FramedPullback.pullbackHomTo x f p hx q = FramedPullback.pullbackHomTo y f p hy q

include eM eN in
theorem existsUnique_framedHom_descent [EffectiveEpi f]
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (hq : CompatibleHom f q) :
    ∃! a : M ⟶ N, (Scheme.Modules.pullback f).map a = q := by
  let r := FramedHom.framedCoefficient (FramedHom.pullbackFrame f eM) (FramedHom.pullbackFrame f eN) q
  have hr : ∀ {T : Scheme.{u}} (x y : T ⟶ X), x ≫ f = y ≫ f → x.appTop r = y.appTop r := by
    intro T x y hxy
    have h := congrArg (FramedHom.framedCoefficient (FramedHom.pullbackFrame (x ≫ f) eM)
      (FramedHom.pullbackFrame (x ≫ f) eN)) (hq x y (x ≫ f) rfl hxy.symm)
    rw [FramedPullback.framedCoefficient_pullbackHomTo, FramedPullback.framedCoefficient_pullbackHomTo] at h
    exact h
  obtain ⟨s, hs, _⟩ := FunctionDescent.existsUnique_function_descent f r hr
  refine ⟨FramedHom.framedHom eM eN s, ?_, ?_⟩
  · change (Scheme.Modules.pullback f).map (FramedHom.framedHom eM eN s) = q
    rw [FramedHom.framedHom_pullback, hs]
    exact FramedHom.framedHom_coefficient (FramedHom.pullbackFrame f eM) (FramedHom.pullbackFrame f eN) q
  · intro a ha
    apply framedPullback_injective f eM eN
    change (Scheme.Modules.pullback f).map a = (Scheme.Modules.pullback f).map (FramedHom.framedHom eM eN s)
    rw [ha, FramedHom.framedHom_pullback, hs]
    exact (FramedHom.framedHom_coefficient (FramedHom.pullbackFrame f eM) (FramedHom.pullbackFrame f eN) q).symm

theorem compatibleHom_inverse
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (he : CompatibleHom f e.hom) : CompatibleHom f e.inv := by
  intro T x y p hx hy
  have h : FramedPullback.pullbackIsoTo x f p hx e = FramedPullback.pullbackIsoTo y f p hy e := Iso.ext (he x y p hx hy)
  exact congrArg Iso.inv h

include eM eN in
/-- Inverse morphisms descend too, so the descended map is an actual
line-bundle isomorphism, with its pullback identified exactly. -/
theorem existsUnique_framedIso_descent [EffectiveEpi f]
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (he : CompatibleHom f e.hom) :
    ∃! a : M ≅ N, (Scheme.Modules.pullback f).map a.hom = e.hom := by
  obtain ⟨a, ha, _⟩ := existsUnique_framedHom_descent f eM eN e.hom he
  obtain ⟨b, hb, _⟩ := existsUnique_framedHom_descent f eN eM e.inv (compatibleHom_inverse f e he)
  have hab : a ≫ b = 𝟙 M := by
    apply framedPullback_injective f eM eM
    change (Scheme.Modules.pullback f).map (a ≫ b) = (Scheme.Modules.pullback f).map (𝟙 M)
    rw [Functor.map_comp, ha, hb, e.hom_inv_id, (Scheme.Modules.pullback f).map_id]
  have hba : b ≫ a = 𝟙 N := by
    apply framedPullback_injective f eN eN
    change (Scheme.Modules.pullback f).map (b ≫ a) = (Scheme.Modules.pullback f).map (𝟙 N)
    rw [Functor.map_comp, hb, ha, e.inv_hom_id, (Scheme.Modules.pullback f).map_id]
  refine ⟨⟨a, b, hab, hba⟩, ha, ?_⟩
  intro c hc
  apply Iso.ext
  exact framedPullback_injective f eM eN (hc.trans ha.symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent
