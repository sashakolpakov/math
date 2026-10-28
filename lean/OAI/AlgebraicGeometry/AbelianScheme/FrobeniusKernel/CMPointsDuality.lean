import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedCartierAdapter
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing

/-! # CM Points Duality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsDuality.Construction

noncomputable section

/-!
Adapter for the native PolarizationDuality clause of the verified CMPoints
statement. The clause is
an explicit conditional input, not an invocation of its unproved theorem.
The induced pairing retains the given polarization and all test schemes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme}

def l45CharactersIso {F G : (Over S)ᵒᵖ ⥤ GrpCat} (e : F ≅ G) :
    PELModuli.CMPoints.DualityPairing.cartierCharacters F ≅ PELModuli.CMPoints.DualityPairing.cartierCharacters G where
  hom := PELModuli.CMPoints.DualityPairing.restrictCharacters e.inv
  inv := PELModuli.CMPoints.DualityPairing.restrictCharacters e.hom
  hom_inv_id := by
    ext T χ
    dsimp only [PELModuli.CMPoints.DualityPairing.restrictCharacters, PELModuli.CMPoints.DualityPairing.cartierCharacters, presheafHom] at *
    ext U x
    change χ.app U (e.inv.app _ (e.hom.app _ x)) = χ.app U x
    exact congrArg (fun z => χ.app U z)
      (congrArg (fun f => (f.app _ ) x) e.hom_inv_id)
  inv_hom_id := by
    ext T χ
    dsimp only [PELModuli.CMPoints.DualityPairing.restrictCharacters, PELModuli.CMPoints.DualityPairing.cartierCharacters, presheafHom] at *
    ext U x
    change χ.app U (e.hom.app _ (e.inv.app _ x)) = χ.app U x
    exact congrArg (fun z => χ.app U z)
      (congrArg (fun f => (f.app _ ) x) e.inv_hom_id)

def groupULiftYonedaIso (G : Grp (Over S)) :
    uliftYoneda.obj G.X ≅ yonedaGrp.obj G ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable {k : Type} [Field k] {g N q : ℕ} {δ : Fin g → ℕ} [Fact q.Prime]
variable {O : Type} [CommRing O]
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O PEL.abelian)
variable (χ χc : O →+* PadicInt q)
variable (hdual : PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ χ χc) (n : ℕ)
variable (B H : Grp (Over (Spec (.of k))))
variable (eB : yonedaGrp.obj B ≅ PELModuli.CMPoints.BlocksProjectors.blockFunctor PEL.abelian ρ χ n)
variable (eH : yonedaGrp.obj H ≅ PELModuli.CMPoints.BlocksProjectors.blockFunctor PEL.abelian ρ χc n)

include hdual eB eH in
/-- The source duality yields a perfect character pairing on the actual
represented block schemes. Its multiplication law follows from the
bilinearity clause for the specified source polarization. -/
theorem exists_l45_sourcePairing :
    ∃ e : (BaseChange.Construction.fppfPoints (Spec (.of k))).obj H.X ≅ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) B,
      ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H.X),
        e.hom.hom.app (op T) (ULift.up (a * b)) =
          e.hom.hom.app (op T) (ULift.up a) * e.hom.hom.app (op T) (ULift.up b) := by
  obtain ⟨ea, hm, _, hi⟩ := hdual n
  let α := Functor.whiskerRight
    (PELModuli.CMPoints.BlocksProjectors.blockInclusion PEL.abelian ρ χc n ≫ PELModuli.CMPoints.DualityPairing.polarizationOnTorsion PEL (q ^ n))
    (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ ea.hom ≫
      PELModuli.CMPoints.DualityPairing.restrictCharacters (PELModuli.CMPoints.BlocksProjectors.blockInclusion PEL.abelian ρ χ n)
  have : IsIso α := hi
  let eb := l45CharactersIso eB
  let β : ((BaseChange.Construction.fppfPoints (Spec (.of k))).obj H.X).obj ⟶
      (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) B).obj :=
    (groupULiftYonedaIso H).hom ≫
      (Functor.isoWhiskerRight eH (forget GrpCat ⋙ uliftFunctor.{1, 0})).hom ≫ α ≫ eb.inv
  have : IsIso β := inferInstanceAs (IsIso
    ((groupULiftYonedaIso H).hom ≫
      (Functor.isoWhiskerRight eH (forget GrpCat ⋙ uliftFunctor.{1, 0})).hom ≫ α ≫ eb.inv))
  let e : (BaseChange.Construction.fppfPoints (Spec (.of k))).obj H.X ≅
      CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) B :=
    { hom := ⟨β⟩
      inv := ⟨inv β⟩
      hom_inv_id := by apply Sheaf.hom_ext; exact IsIso.hom_inv_id β
      inv_hom_id := by apply Sheaf.hom_ext; exact IsIso.inv_hom_id β }
  refine ⟨e, ?_⟩
  intro T a b
  change (β.app (op T) (ULift.up (a * b)) : CharacterGroups.Construction.CharacterSections B T) =
    (β.app (op T) (ULift.up a) : CharacterGroups.Construction.CharacterSections B T) *
      (β.app (op T) (ULift.up b) : CharacterGroups.Construction.CharacterSections B T)
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  let t : yonedaGrp.obj H ⟶ PEL.dual.abelian.torsionFunctor (q ^ n) :=
    eH.hom ≫ PELModuli.CMPoints.BlocksProjectors.blockInclusion PEL.abelian ρ χc n ≫ PELModuli.CMPoints.DualityPairing.polarizationOnTorsion PEL (q ^ n)
  let y := (PELModuli.CMPoints.BlocksProjectors.blockInclusion PEL.abelian ρ χ n).app (op U.unop.left)
    (eB.hom.app (op U.unop.left) x)
  change ((ea.hom.app (op T) (ULift.up (t.app (op T) (a * b)))).app U) y =
    ((ea.hom.app (op T) (ULift.up (t.app (op T) a))).app U) y *
      ((ea.hom.app (op T) (ULift.up (t.app (op T) b))).app U) y
  exact (congrArg (fun z => ((ea.hom.app (op T) (ULift.up z)).app U) y)
    ((t.app (op T)).hom.map_mul a b)).trans (hm T _ _ U.unop y)

variable (P : CartierModel.Construction.CartierCoordinates (.of k) B)

/-- The pairing field required by the native block kernel is constructed
from CMPoints's actual polarized torsion duality. -/
def l45PolarizedCartierGroupIso : H ≅ P.dualGroup := by
  let e := Classical.choose (exists_l45_sourcePairing PEL ρ χ χc hdual n B H eB eH)
  have hm := Classical.choose_spec (exists_l45_sourcePairing PEL ρ χ χc hdual n B H eB eH)
  exact P.sourcePairingGroupIso e hm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsDuality.Construction
