import OAI.AlgebraicGeometry.PELModuli.CMPoints.GenericProjectionMaps

/-! # Fixed Arithmetic Isomorphisms -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedArithmeticIsomorphisms

noncomputable section

/-! Generic isomorphisms between specified smooth arithmetic models
extend after enlarging the denominator. Inverse identities follow from
the actual generic projections, not from a model uniqueness assumption. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem iso_between_fixed_arithmetic_models_spreads
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ)
    (X Y : Over B.base) [Smooth X.hom] [Smooth Y.hom]
    [IsSeparated X.hom] [IsSeparated Y.hom]
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    {G H : Over (Spec (.of B.extension.carrier))}
    (p : G.left ⟶ X.left) (q : H.left ⟶ Y.left)
    (hp : IsPullback p G.hom X.hom B.generic)
    (hq : IsPullback q H.hom Y.hom B.generic) (e : G ≅ H) :
    ∃ (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D),
      ∃ eD : (Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj X ≅
        (Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj Y,
        FixedArithmeticDiagrams.arithmeticModelProjection B X p hp.w D hD hdiv ≫ eD.hom.left =
          e.hom.left ≫ FixedArithmeticDiagrams.arithmeticModelProjection B Y q hq.w D hD hdiv := by
  let Z : Bool → Over B.base | false => X | true => Y
  let U : Bool → Over (Spec (.of B.extension.carrier)) | false => G | true => H
  let π : ∀ i, (U i).left ⟶ (Z i).left | false => p | true => q
  have hπ : ∀ i, IsPullback (π i) (U i).hom (Z i).hom B.generic
    | false => hp | true => hq
  have hZ : ∀ i, ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (Z i).hom
    | false => hX | true => hY
  let a : ∀ i : Bool, U i ⟶ U (!i) | false => e.hom | true => e.inv
  obtain ⟨D, hD, hdiv, b, hb⟩ := FixedArithmeticDiagrams.finite_morphisms_between_fixed_arithmetic_models_spread
    B id Bool.not Z U hZ π hπ a
  let B' := B.withDenominator D hD
  let u := ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv
  let XD := (Over.pullback u).obj X
  let YD := (Over.pullback u).obj Y
  let pD := FixedArithmeticDiagrams.arithmeticModelProjection B X p hp.w D hD hdiv
  let qD := FixedArithmeticDiagrams.arithmeticModelProjection B Y q hq.w D hD hdiv
  let f : XD ⟶ YD := b false
  let g : YD ⟶ XD := b true
  have hf : pD ≫ f.left = e.hom.left ≫ qD := hb false
  have hg : qD ≫ g.left = e.inv.left ≫ pD := hb true
  let : IsDomain B'.R := Function.Injective.isDomain B'.toField B'.toField_injective
  let : IsReduced B'.base := inferInstanceAs (IsReduced (Spec (.of B'.R)))
  let : IsLocallyNoetherian B'.base := inferInstanceAs (IsLocallyNoetherian (Spec (.of B'.R)))
  let : IsDominant B'.generic := B'.generic_dominant
  let : Smooth XD.hom := inferInstanceAs (Smooth (pullback.snd X.hom u))
  let : Smooth YD.hom := inferInstanceAs (Smooth (pullback.snd Y.hom u))
  let : IsSeparated XD.hom := inferInstanceAs (IsSeparated (pullback.snd X.hom u))
  let : IsSeparated YD.hom := inferInstanceAs (IsSeparated (pullback.snd Y.hom u))
  have hfg : f ≫ g = 𝟙 XD := by
    apply GenericProjectionMaps.smooth_hom_eq_of_generic_projection B'.generic pD
      (GenericProjectionMaps.arithmeticModelProjection_cartesian B X p hp D hD hdiv)
    change pD ≫ (f.left ≫ g.left) = pD ≫ 𝟙 XD.left
    rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc,
      Over.hom_left_inv_left, Category.id_comp, Category.comp_id]
  have hgf : g ≫ f = 𝟙 YD := by
    apply GenericProjectionMaps.smooth_hom_eq_of_generic_projection B'.generic qD
      (GenericProjectionMaps.arithmeticModelProjection_cartesian B Y q hq D hD hdiv)
    change qD ≫ (g.left ≫ f.left) = qD ≫ 𝟙 YD.left
    rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc,
      Over.inv_left_hom_left, Category.id_comp, Category.comp_id]
  exact ⟨D, hD, hdiv, ⟨f, g, hfg, hgf⟩, hf⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedArithmeticIsomorphisms
