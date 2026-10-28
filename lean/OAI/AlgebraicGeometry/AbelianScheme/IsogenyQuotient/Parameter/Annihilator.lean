import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.IntrinsicSubgroup

/-! # Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.Annihilator.Construction

noncomputable section

/-!
Apply actual CartierDuality annihilator duality over an arbitrary parameter scheme.
The source pairing is the constructed base change, and the finite
subgroup is the original model transported through its exact inclusion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative

universe u

variable {S : Scheme.{u}} (G K : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj K.X]
  (P : Over S) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) (R : F.Model)

theorem parameterNativeSubgroup_annihilator
    [IsFinite ((Over.pullback P.hom).mapGrp.obj G).X.hom]
    [Flat ((Over.pullback P.hom).mapGrp.obj G).X.hom]
    [LocallyOfFinitePresentation ((Over.pullback P.hom).mapGrp.obj G).X.hom]
    (b : Annihilator.Construction.SchemeBicharacter (A := ((Over.pullback P.hom).mapGrp.obj G).X)
      (B := ((Over.pullback P.hom).mapGrp.obj K).X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver P.left).X))
    (hb : b.toSheafPairing.IsPerfect) :
    let H := Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup (IntrinsicSubgroup.Construction.parameterNativeSubgroupInclusion G P F R).hom.hom
    Nonempty (b.relativeAnnihilator H).Model ∧
      b.flip.relativeAnnihilator (b.relativeAnnihilator H) = H := by
  have hgeom := Subgroup.Construction.subgroupGroupScheme_finiteLocallyFree F R
  let : IsFinite (Subgroup.Construction.subgroupGroupScheme F R).X.hom := hgeom.1
  let : Flat (Subgroup.Construction.subgroupGroupScheme F R).X.hom := hgeom.2.1
  let : LocallyOfFinitePresentation (Subgroup.Construction.subgroupGroupScheme F R).X.hom := hgeom.2.2
  exact b.commGroupImage_relative_annihilator_model_and_double (Subgroup.Construction.subgroupGroupScheme F R)
    (IntrinsicSubgroup.Construction.parameterNativeSubgroupInclusion G P F R) hb

include R in
theorem relativeParameter_annihilator_from_perfect_pairing
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := K.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (he : e.toSheafPairing.IsPerfect) :
    let eP := PairingBaseChange.Construction.nativePairingPullback P.hom G K e
    let FP := Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F
    Nonempty (eP.relativeAnnihilator FP).Model ∧
      eP.flip.relativeAnnihilator (eP.relativeAnnihilator FP) = FP := by
  let eP := PairingBaseChange.Construction.nativePairingPullback P.hom G K e
  let : IsFinite ((Over.pullback P.hom).mapGrp.obj G).X.hom :=
    inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd G.X.hom P.hom))
  let : Flat ((Over.pullback P.hom).mapGrp.obj G).X.hom :=
    inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd G.X.hom P.hom))
  let : LocallyOfFinitePresentation ((Over.pullback P.hom).mapGrp.obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd G.X.hom P.hom))
  have h := parameterNativeSubgroup_annihilator G K P F R eP
    (PairingBaseChange.Construction.nativePairingPullback_isPerfect P.hom G K e he)
  have hi := IntrinsicSubgroup.Construction.parameterNativeSubgroup_image G P F R
  have ha := congrArg eP.relativeAnnihilator hi
  exact ⟨ha ▸ h.1, (congrArg eP.flip.relativeAnnihilator ha).symm.trans (h.2.trans hi)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.Annihilator.Construction
