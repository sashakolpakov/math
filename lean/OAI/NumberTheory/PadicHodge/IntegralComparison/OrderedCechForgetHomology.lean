import OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechForget

/-! # Ordered Cech Forget Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCechForgetHomology.AbelianSupported

noncomputable section

/-! The canonical global supported lift has the same inverse-forget
normalization on the original cohomology groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

private theorem map_square {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B T E : C} (a : A ⟶ B) (b : B ⟶ T)
    (c : A ⟶ E) (d : E ⟶ T) (h : a ≫ b = c ≫ d) :
    H.map a ≫ H.map b = H.map c ≫ H.map d :=
  (H.map_comp a b).symm.trans ((congrArg H.map h).trans (H.map_comp c d))

universe u
variable (D : Type (u+1)) [Category.{u} D] [Abelian D] [HasLimitsOfSize.{u,u} D]
  (X : TopCat.{u})
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Opens X)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)
  (hO : ∀ i, F.obj (U i) ≤ O)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index ι q,
    IsZero (((SupportedOrderedCechEdge.Abelian.presheafComplex D X F K).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))
  (hglobal : ∀ q, IsZero ((K.X q).obj.obj (op O)))

abbrev global_lift_homology (q : ℕ) := map_square
  (HomologicalComplex.homologyFunctor D (.up ℕ) q) _ _ _ _
  (SupportedOrderedCechForget.Abelian.global_lift_factorization D X F U O K hO hzero hglobal)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCechForgetHomology.AbelianSupported
