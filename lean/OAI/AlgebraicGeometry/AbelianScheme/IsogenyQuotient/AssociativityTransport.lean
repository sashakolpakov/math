import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition

/-! # Associativity Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityTransport.Construction

noncomputable section

/-! Consistent changes of the six line fibers reflect associativity
of the four actual bilinear structure maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport

universe u

theorem lineBilinear_associative_of_transport {X : Scheme.{u}}
    {M N P MN NP Q M' N' P' MN' NP' Q' : X.Modules}
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N P NP) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M NP Q)
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (e : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN P Q)
    (aM : M ≅ M') (aN : N ≅ N') (aP : P ≅ P')
    (aMN : MN ≅ MN') (aNP : NP ≅ NP') (aQ : Q ≅ Q')
    (h : ∀ (U : X.Opens) (m : Γ(M', U)) (n : Γ(N', U)) (p : Γ(P', U)),
      (Picard.PoincareBundle.Bilinear.Transport.transport c aM aNP aQ).app U m ((Picard.PoincareBundle.Bilinear.Transport.transport b aN aP aNP).app U n p) =
        (Picard.PoincareBundle.Bilinear.Transport.transport e aMN aP aQ).app U ((Picard.PoincareBundle.Bilinear.Transport.transport d aM aN aMN).app U m n) p)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    c.app U m (b.app U n p) = e.app U (d.app U m n) p := by
  have hr := Picard.PoincareBundle.Bilinear.AlgebraTransport.associative
    (Picard.PoincareBundle.Bilinear.Transport.transport b aN aP aNP) (Picard.PoincareBundle.Bilinear.Transport.transport c aM aNP aQ)
    (Picard.PoincareBundle.Bilinear.Transport.transport d aM aN aMN) (Picard.PoincareBundle.Bilinear.Transport.transport e aMN aP aQ)
    aM.symm aN.symm aP.symm aMN.symm aNP.symm aQ.symm h U m n p
  simpa only [Picard.PoincareBundle.Bilinear.TransportComposition.transport_trans, Iso.self_symm_id,
    Picard.PoincareBundle.Bilinear.TransportComposition.transport_refl] using hr

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityTransport.Construction
