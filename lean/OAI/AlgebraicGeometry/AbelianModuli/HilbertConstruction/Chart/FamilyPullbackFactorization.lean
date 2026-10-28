import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyTransport

/-! # Family Pullback Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.FamilyPullbackFactorization

noncomputable section

/-! The original chart-family transport can be computed using any
intersection lift with the specified two projections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

theorem chartPullbackLift_exists
    {C : Type u} [Category.{v} C] {W A B Z T : C}
    {l : W ⟶ A} {r : W ⟶ B} {p : A ⟶ Z} {q : B ⟶ Z}
    (H : IsPullback l r p q) (a : T ⟶ A) (b : T ⟶ B)
    (h : a ≫ p = b ≫ q) : ∃ c : T ⟶ W, c ≫ l = a ∧ c ≫ r = b :=
  ⟨H.lift a b h, H.lift_fst a b h, H.lift_snd a b h⟩

theorem chartFamilyPullbackTransport_factor
    {S : Scheme.{u}} {W A B Z : Over S}
    {l : W ⟶ A} {r : W ⟶ B} {p : A ⟶ Z} {q : B ⟶ Z}
    (H : IsPullback l r p q) (F : Over A.left) (G : Over B.left)
    (e : (Over.pullback l.left).obj F ≅ (Over.pullback r.left).obj G)
    {T : Over S} (a : T ⟶ A) (b : T ⟶ B) (h : a ≫ p = b ≫ q)
    (c : T ⟶ W) (hL : c ≫ l = a) (hR : c ≫ r = b) :
    StableHilbert.FamilyTransport.chartFamilyPullbackTransport H F G e a b h =
      ((Over.pullbackComp c.left l.left).symm.app F ≪≫
        eqToIso (congrArg (fun f : T.left ⟶ A.left => (Over.pullback f).obj F)
          (congrArg Over.Hom.left hL))).symm ≪≫
      (Over.pullback c.left).mapIso e ≪≫
      ((Over.pullbackComp c.left r.left).symm.app G ≪≫
        eqToIso (congrArg (fun f : T.left ⟶ B.left => (Over.pullback f).obj G)
          (congrArg Over.Hom.left hR))) := by
  have hc : c = H.lift a b h := by
    apply H.hom_ext
    · exact hL.trans (H.lift_fst a b h).symm
    · exact hR.trans (H.lift_snd a b h).symm
  subst c
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.FamilyPullbackFactorization
