import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

/-! # Action Laws -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ActionLaws

noncomputable section

/-!
# Associative bilinear multiplication and normalized sections give action laws
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {X : Scheme.{u}}

/-- The bilinear unit identity implies the actual unit identity for the induced transport morphism. -/
theorem contraction_unit {M N : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N N) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (h : ∀ (U : X.Opens) (n : Γ(N, U)), β.app U (s.app U (1 : Γ(X, U))) n = n) :
    Contraction.contractLeft β s = 𝟙 N := by
  apply Scheme.Modules.hom_ext
  intro U
  ext n
  exact (Contraction.contractLeft_app β s U n).trans (h U n)

/-- Associative multiplication and multiplicative normalized sections imply composition of the induced transports. -/
theorem contraction_comp {K L M P Q R : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap K M P) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L P R)
    (δ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L K Q) (ε : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap Q M R)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ K) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L) (u : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ Q)
    (hassoc : ∀ (U : X.Opens) (l : Γ(L, U)) (k : Γ(K, U)) (m : Γ(M, U)),
      γ.app U l (β.app U k m) = ε.app U (δ.app U l k) m)
    (hmul : ∀ U : X.Opens, δ.app U (t.app U (1 : Γ(X, U))) (s.app U (1 : Γ(X, U))) =
      u.app U (1 : Γ(X, U))) :
    Contraction.contractLeft β s ≫ Contraction.contractLeft γ t = Contraction.contractLeft ε u := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change (Contraction.contractLeft γ t).app U ((Contraction.contractLeft β s).app U m) = (Contraction.contractLeft ε u).app U m
  rw [Contraction.contractLeft_app, Contraction.contractLeft_app, Contraction.contractLeft_app, hassoc, hmul]

/-- An interchange identity for the two bilinear multiplications gives commuting transport maps. -/
theorem contraction_interchange {K L M P Q R : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap K M P) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L P R)
    (δ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M Q) (ε : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap K Q R)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ K) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L)
    (h : ∀ (U : X.Opens) (m : Γ(M, U)),
      γ.app U (t.app U (1 : Γ(X, U))) (β.app U (s.app U (1 : Γ(X, U))) m) =
        ε.app U (s.app U (1 : Γ(X, U))) (δ.app U (t.app U (1 : Γ(X, U))) m)) :
    Contraction.contractLeft β s ≫ Contraction.contractLeft γ t = Contraction.contractLeft δ t ≫ Contraction.contractLeft ε s := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change (Contraction.contractLeft γ t).app U ((Contraction.contractLeft β s).app U m) =
    (Contraction.contractLeft ε s).app U ((Contraction.contractLeft δ t).app U m)
  rw [Contraction.contractLeft_app, Contraction.contractLeft_app, Contraction.contractLeft_app, Contraction.contractLeft_app]
  exact h U m

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ActionLaws
