import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingAdjoints

/-! # Sheaf Pairing Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingTransport.Construction

/-! Transport of a polarization pairing through its actual dual square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem sheafPolarizationPairing_transport {S : Scheme} {G H DG DH : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (eG : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G DG) (eH : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing H DH)
    (f : G ⟶ H) (d : DH ⟶ DG) (lG : G ⟶ DG) (lH : H ⟶ DH)
    (he : ∀ (T : Over S) (x : G.obj.obj (.op T)) (y : DH.obj.obj (.op T)),
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue H T (eH.rightAdjoint.hom.app (.op T) y) (f.hom.app (.op T) x) =
        CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (eG.rightAdjoint.hom.app (.op T) (d.hom.app (.op T) y)) x)
    (hl : f ≫ lH ≫ d = lG)
    (T : Over S) (x y : G.obj.obj (.op T)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue H T
      ((eH.restrict (𝟙 H) lH).rightAdjoint.hom.app (.op T) (f.hom.app (.op T) y))
      (f.hom.app (.op T) x) =
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T ((eG.restrict (𝟙 G) lG).rightAdjoint.hom.app (.op T) y) x := by
  rw [SheafPairingAdjoints.Construction.pairing_restrict_rightAdjoint, SheafPairingAdjoints.Construction.pairing_restrict_rightAdjoint]
  change CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue H T (eH.rightAdjoint.hom.app (.op T)
    (lH.hom.app (.op T) (f.hom.app (.op T) y))) (f.hom.app (.op T) x) = _
  rw [he]
  have hy := congrArg (fun t => t.hom.app (.op T) y) hl
  exact congrArg (fun z => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (eG.rightAdjoint.hom.app (.op T) z) x) hy

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingTransport.Construction
