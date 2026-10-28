import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorRepresentation

/-! # Polarized Cartier Adapter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
Turn a perfect source character pairing into the native Cartier group
isomorphism used by the block kernels. Multiplication is proved from the
bilinearity of that pairing, rather than added as compatibility data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : CommRingCat.{u}} {G H : Grp (Over (Spec R))}
variable (P : CartierModel.Construction.CartierCoordinates R G)
variable (e : (BaseChange.Construction.fppfPoints (Spec R)).obj H.X ≅ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G)

def CartierModel.Construction.CartierCoordinates.sourcePairingSchemeIso : H.X ≅ P.dualGroup.X :=
  (Functor.FullyFaithful.ofFullyFaithful (BaseChange.Construction.fppfPoints (Spec R))).preimageIso
    (e ≪≫ P.characterIso.symm)

theorem CartierModel.Construction.CartierCoordinates.sourcePairingSchemeIso_action (T : Over (Spec R)) (a : T ⟶ H.X) :
    P.pointsEquiv T (a ≫ (P.sourcePairingSchemeIso e).hom) =
      e.hom.hom.app (op T) (ULift.up a) := by
  let F := BaseChange.Construction.fppfPoints (Spec R)
  let χ : F.obj P.dualGroup.X ⟶ CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G := P.characterIso.hom
  have hmap : F.map (P.sourcePairingSchemeIso e).hom ≫ χ = e.hom := by
    have h := (Functor.FullyFaithful.ofFullyFaithful F).map_preimage
      (e.hom ≫ P.characterIso.inv)
    exact (congrArg (fun f => f ≫ χ) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => e.hom ≫ f) P.characterIso.inv_hom_id).trans (Category.comp_id _)))
  exact congrArg (fun f => f.hom.app (op T) (ULift.up a)) hmap

variable (hmul : ∀ (T : Over (Spec R)) (a b : T ⟶ H.X),
  e.hom.hom.app (op T) (ULift.up (a * b)) =
    e.hom.hom.app (op T) (ULift.up a) * e.hom.hom.app (op T) (ULift.up b))

include hmul in
theorem CartierModel.Construction.CartierCoordinates.sourcePairingSchemeIso_isMonHom : IsMonHom (P.sourcePairingSchemeIso e).hom := by
  let i := (P.sourcePairingSchemeIso e).hom
  have hm (T : Over (Spec R)) (a b : T ⟶ H.X) :
      (a * b) ≫ i = (a ≫ i) * (b ≫ i) := by
    apply (P.pointsEquiv T).injective
    exact (P.sourcePairingSchemeIso_action e T (a * b)).trans
      ((hmul T a b).trans
        ((congrArg₂ (· * ·) (P.sourcePairingSchemeIso_action e T a).symm
          (P.sourcePairingSchemeIso_action e T b).symm).trans
            ((P.pointsEquiv T).map_mul _ _).symm))
  apply RepresentedGroups.Construction.isMonHom_of_point_operations i
  · intro T
    let z := (1 : T ⟶ H.X) ≫ i
    have h : z = z * z :=
      (congrArg (fun a : T ⟶ H.X => a ≫ i) (one_mul 1)).symm.trans (hm T 1 1)
    exact (mul_left_cancel ((mul_one z).trans h)).symm
  · exact hm

/-- Perfect bilinear source pairing yields the actual group-scheme
Cartier identification, preserving its given character evaluations. -/
def CartierModel.Construction.CartierCoordinates.sourcePairingGroupIso : H ≅ P.dualGroup := by
  have : IsMonHom (P.sourcePairingSchemeIso e).hom := P.sourcePairingSchemeIso_isMonHom e hmul
  exact Grp.mkIso (P.sourcePairingSchemeIso e)

theorem CartierModel.Construction.CartierCoordinates.sourcePairingGroupIso_action (T : Over (Spec R)) (a : T ⟶ H.X) :
    P.pointsEquiv T (a ≫ (P.sourcePairingGroupIso e hmul).hom.hom.hom) =
      e.hom.hom.app (op T) (ULift.up a) :=
  P.sourcePairingSchemeIso_action e T a

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
