import OAI.RepresentationTheory.Theta.Geometric.FppfPicardLocality

/-! # Fppf Pair Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric.FppfPairLift

noncomputable section

/-! Two actual test-scheme parameters admit simultaneous lifts after
one faithfully flat, locally finitely presented cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_fppf_pair_lift {S : Scheme.{u}} {P' P T : Over S}
    (p : P' ⟶ P) [Flat p.left] [LocallyOfFinitePresentation p.left] [Surjective p.left]
    (a b : T ⟶ P) :
    ∃ (U : Over S) (u : U ⟶ T) (x y : U ⟶ P'),
      Flat u.left ∧ LocallyOfFinitePresentation u.left ∧ Surjective u.left ∧
        u ≫ a = x ≫ p ∧ u ≫ b = y ≫ p := by
  obtain ⟨V, v, x, hvF, hvP, hvS, hxa⟩ := FppfPicardLocality.exists_fppf_test_lift p a
  obtain ⟨U, u, y, huF, huP, huS, hyb⟩ := FppfPicardLocality.exists_fppf_test_lift p (v ≫ b)
  let : Flat v.left := hvF
  let : LocallyOfFinitePresentation v.left := hvP
  let : Flat u.left := huF
  let : LocallyOfFinitePresentation u.left := huP
  refine ⟨U, u ≫ v, u ≫ x, y, ?_, ?_, ?_, ?_, ?_⟩
  · change Flat (u.left ≫ v.left)
    infer_instance
  · change LocallyOfFinitePresentation (u.left ≫ v.left)
    infer_instance
  · exact ⟨hvS.surj.comp huS.surj⟩
  · exact (Category.assoc u v a).trans ((congrArg (fun f => u ≫ f) hxa).trans (Category.assoc u x p).symm)
  · exact (Category.assoc u v b).trans hyb

end

end OAI.RepresentationTheory.Theta.Geometric.FppfPairLift
