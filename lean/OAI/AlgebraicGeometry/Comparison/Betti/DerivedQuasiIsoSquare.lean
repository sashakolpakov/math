import OAI.AlgebraicGeometry.Comparison.Betti.CoefficientDerivedNaturality

/-! # Derived Quasi Iso Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DerivedQuasiIsoSquare.Ext

noncomputable section

/-! Bijectivity of the normalized derived comparison descends along proved quasi-isomorphisms in a commuting square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u u' v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : C) (A' : D) (a : A' ⟶ F.obj A)
  {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
  (β : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
  (β' : (F.mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
  (e : K ⟶ K') (d : L ⟶ L')
  (h : (F.mapHomologicalComplex (.up ℤ)).map e ≫ β' = β ≫ d)

include h in
theorem coefficientDerivedMap_bijective_of_quasiIso_square (he : QuasiIso e) (hd : QuasiIso d) (n : ℤ)
    (hβ' : Function.Bijective (Acyclic.Functor.Ext.coefficientDerivedMap F A A' a K' L' β' n)) :
    Function.Bijective (Acyclic.Functor.Ext.coefficientDerivedMap F A A' a K L β n) := by
  have hQe : IsIso (DerivedCategory.Q.map e) := (DerivedCategory.isIso_Q_map_iff_quasiIso C e).mpr he
  have hQd : IsIso (DerivedCategory.Q.map d) := (DerivedCategory.isIso_Q_map_iff_quasiIso D d).mpr hd
  let s := Iso.homCongr (Iso.refl ((DerivedCategory.singleFunctor C 0).obj A))
    ((shiftFunctor (DerivedCategory C) n).mapIso (asIso (DerivedCategory.Q.map e)))
  let t := Iso.homCongr (Iso.refl ((DerivedCategory.singleFunctor D 0).obj A'))
    ((shiftFunctor (DerivedCategory D) n).mapIso (asIso (DerivedCategory.Q.map d)))
  let g := Acyclic.Functor.Ext.coefficientDerivedMap F A A' a K L β n
  let g' := Acyclic.Functor.Ext.coefficientDerivedMap F A A' a K' L' β' n
  have hn (x) : t (g x) = g' (s x) := by
    change (𝟙 _ ≫ g x ≫ (DerivedCategory.Q.map d)⟦n⟧') =
      g' (𝟙 _ ≫ x ≫ (DerivedCategory.Q.map e)⟦n⟧')
    rw [Category.id_comp, Category.id_comp]
    exact (CoefficientDerivedNaturality.Ext.coefficientDerivedMap_naturality F β β' e d h A A' a n x).symm
  constructor
  · intro x y hxy
    apply s.injective
    apply hβ'.injective
    exact (hn x).symm.trans ((congrArg t hxy).trans (hn y))
  · intro y
    obtain ⟨z', hz'⟩ := hβ'.surjective (t y)
    obtain ⟨z, hz⟩ := s.surjective z'
    refine ⟨z, t.injective ?_⟩
    exact (hn z).trans ((congrArg g' hz).trans hz')

end

end OAI.AlgebraicGeometry.Comparison.Betti.DerivedQuasiIsoSquare.Ext
