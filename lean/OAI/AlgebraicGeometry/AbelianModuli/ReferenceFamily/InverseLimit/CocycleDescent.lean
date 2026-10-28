import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenUnitEquations

/-! # Cocycle Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleDescent

noncomputable section

/-! A finite regular-unit cocycle on the limit of affine transition
maps descends, with its literal equations, to one actual scheme stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {I : Type} [Category.{0} I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    (hc : IsLimit c) [IsCofiltered I] [Quiver.IsThin I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
theorem exists_limit_open_cocycle_stage {J : Type} [Fintype J] {i : I}
    (U : J → (D.obj i).Opens)
    (h₂ : ∀ a b, IsAffineOpen (U a ⊓ U b))
    (h₃ : ∀ a b d, IsAffineOpen ((U a ⊓ U b) ⊓ U d))
    (r : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => c.π.app i ⁻¹ᵁ U a))
    (hr : Open.TransitionCocycle.OpenTransitionCocycle (fun a => c.π.app i ⁻¹ᵁ U a) r) :
    ∃ (k : Over i) (q : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map k.hom ⁻¹ᵁ U a)),
      Open.TransitionCocycle.OpenTransitionCocycle (fun a => D.map k.hom ⁻¹ᵁ U a) q ∧
        CocycleMaps.openCoefficientsConePullback D c U k q = r := by
  classical
  obtain ⟨k, v, hv⟩ := OpenUnits.exists_finite_limit_open_units_stage D c hc
    (fun ab : J × J => U ab.1 ⊓ U ab.2) (fun ab => h₂ ab.1 ab.2)
    (fun ab => r ab.1 ab.2)
  let q : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map k.hom ⁻¹ᵁ U a) := fun a b => v (a, b)
  have hq : CocycleMaps.openCoefficientsConePullback D c U k q = r := by
    funext a b
    exact hv (a, b)
  let W : J × J × J → (D.obj i).Opens := fun t => (U t.1 ⊓ U t.2.1) ⊓ U t.2.2
  let a : ∀ t, Γ((opensDiagram D i (W t)).obj k, ⊤)ˣ := fun t =>
    Open.TransitionCocycle.openTransitionOn (fun j => D.map k.hom ⁻¹ᵁ U j) q t.1 t.2.1 (D.map k.hom ⁻¹ᵁ W t)
      ((D.map k.hom).preimage_mono (show W t ≤ U t.1 from inf_le_left.trans inf_le_left))
      ((D.map k.hom).preimage_mono (show W t ≤ U t.2.1 from inf_le_left.trans inf_le_right)) *
    Open.TransitionCocycle.openTransitionOn (fun j => D.map k.hom ⁻¹ᵁ U j) q t.2.1 t.2.2 (D.map k.hom ⁻¹ᵁ W t)
      ((D.map k.hom).preimage_mono (show W t ≤ U t.2.1 from inf_le_left.trans inf_le_right))
      ((D.map k.hom).preimage_mono (show W t ≤ U t.2.2 from inf_le_right))
  let b : ∀ t, Γ((opensDiagram D i (W t)).obj k, ⊤)ˣ := fun t =>
    Open.TransitionCocycle.openTransitionOn (fun j => D.map k.hom ⁻¹ᵁ U j) q t.1 t.2.2 (D.map k.hom ⁻¹ᵁ W t)
      ((D.map k.hom).preimage_mono (show W t ≤ U t.1 from inf_le_left.trans inf_le_left))
      ((D.map k.hom).preimage_mono (show W t ≤ U t.2.2 from inf_le_right))
  have hab (t : J × J × J) :
      Units.map ((opensCone D c i (W t)).π.app k).appTop.hom.toMonoidHom (a t) =
        Units.map ((opensCone D c i (W t)).π.app k).appTop.hom.toMonoidHom (b t) := by
    have hx := CocycleMaps.openTransitionOn_cone D c U k q t.1 t.2.1 (W t)
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    have hy := CocycleMaps.openTransitionOn_cone D c U k q t.2.1 t.2.2 (W t)
      (inf_le_left.trans inf_le_right) inf_le_right
    have hz := CocycleMaps.openTransitionOn_cone D c U k q t.1 t.2.2 (W t)
      (inf_le_left.trans inf_le_left) inf_le_right
    have hqr : Open.TransitionCocycle.OpenTransitionCocycle (fun a => c.π.app i ⁻¹ᵁ U a)
        (CocycleMaps.openCoefficientsConePullback D c U k q) := hq.symm ▸ hr
    exact ((Units.map ((opensCone D c i (W t)).π.app k).appTop.hom.toMonoidHom).map_mul _ _).trans
      ((congrArg₂ (fun x y : Γ((opensCone D c i (W t)).pt, ⊤)ˣ => x * y) hx hy).trans
        ((hqr t.1 t.2.1 t.2.2).trans hz.symm))
  obtain ⟨l, f, hf⟩ := OpenUnitEquations.exists_finite_limit_open_unit_equations D c hc W
    (fun t => h₃ t.1 t.2.1 t.2.2) k a b hab
  refine ⟨l, CocycleMaps.openCoefficientsDiagramPullback D U f q, ?_,
    (CocycleMaps.openCoefficientsConePullback_diagram D c U f q).trans hq⟩
  intro x y z
  have h := hf (x, y, z)
  have hx := CocycleMaps.openTransitionOn_diagram D U f q x y (W (x, y, z))
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
  have hy := CocycleMaps.openTransitionOn_diagram D U f q y z (W (x, y, z))
    (inf_le_left.trans inf_le_right) inf_le_right
  have hz := CocycleMaps.openTransitionOn_diagram D U f q x z (W (x, y, z))
    (inf_le_left.trans inf_le_left) inf_le_right
  exact (congrArg₂ (fun u v : Γ((opensDiagram D i (W (x, y, z))).obj l, ⊤)ˣ => u * v) hx hy).symm.trans
    (((Units.map ((opensDiagram D i (W (x, y, z))).map f).appTop.hom.toMonoidHom).map_mul _ _).symm.trans
      (h.trans hz))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleDescent
