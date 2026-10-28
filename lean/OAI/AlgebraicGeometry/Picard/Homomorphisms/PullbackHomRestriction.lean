import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomImageRestriction
import OAI.AlgebraicGeometry.Picard.Homomorphisms.RestrictedHomTransport
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PullbackHomGluing

/-! # Pullback Hom Restriction -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PullbackHomRestriction

noncomputable section

/-! Internal-Hom sections restrict by the same canonical transport that
appears in the faithful-flat descent matching equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)

def pullbackHomOnImageEquiv :
    ((Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) ≃
      Γ(InternalHom.Construction.moduleInternalHom M N, f ''ᵁ (⊤ : X.Opens)) :=
  (Iso.homCongr ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
    ((Scheme.Modules.restrictFunctorIsoPullback f).app N).symm).trans (HomOnOpenImages.Construction.moduleHomOnImageEquiv f M N)

variable {Z : Scheme.{u}} (g : Y ⟶ Z) [IsOpenImmersion g] (L K : Z.Modules)

theorem pullbackHomOnImageEquiv_transport
    (b : (Scheme.Modules.pullback g).obj L ⟶ (Scheme.Modules.pullback g).obj K) :
    pullbackHomOnImageEquiv (f ≫ g) L K (ModuleHomTransport.Construction.moduleHomTransport g b f (f ≫ g) rfl) =
      (InternalHom.Construction.moduleInternalHom L K).presheaf.map (HomImageRestriction.Construction.compositeImageInclusion f g).op
        (pullbackHomOnImageEquiv g L K b) :=
  (congrArg (HomOnOpenImages.Construction.moduleHomOnImageEquiv (f ≫ g) L K) (RestrictedHomTransport.Construction.restriction_compare_transport f g b)).trans
    (HomImageRestriction.Construction.moduleHomOnImageEquiv_comp f g L K _)

def transportImageInclusion (q : X ⟶ Z) [IsOpenImmersion q] (hq : f ≫ g = q) :
    q ''ᵁ (⊤ : X.Opens) ⟶ g ''ᵁ (⊤ : Y.Opens) := by
  cases hq
  exact HomImageRestriction.Construction.compositeImageInclusion f g

theorem pullbackHomOnImageEquiv_transport_eq
    (b : (Scheme.Modules.pullback g).obj L ⟶ (Scheme.Modules.pullback g).obj K)
    (q : X ⟶ Z) [IsOpenImmersion q] (hq : f ≫ g = q) :
    pullbackHomOnImageEquiv q L K (ModuleHomTransport.Construction.moduleHomTransport g b f q hq) =
      (InternalHom.Construction.moduleInternalHom L K).presheaf.map (transportImageInclusion f g q hq).op
        (pullbackHomOnImageEquiv g L K b) := by
  cases hq
  exact pullbackHomOnImageEquiv_transport f g L K b

theorem presheaf_section_cast_map {W : Scheme.{u}} (F : TopCat.Presheaf AddCommGrpCat W)
    {U V U' V' : W.Opens} (hU : U = U') (hV : V = V') (i : V ⟶ U) (i' : V' ⟶ U')
    (a : F.obj (op U)) :
    Equiv.cast (congrArg (fun V : W.Opens => (F.obj (op V) : Type u)) hV) (F.map i.op a) =
      F.map i'.op (Equiv.cast (congrArg (fun U : W.Opens => (F.obj (op U) : Type u)) hU) a) := by
  cases hU
  cases hV
  have hi : i = i' := Subsingleton.elim _ _
  cases hi
  rfl

theorem pullbackHomOnOpenEquiv_restrict {W : Scheme.{u}} (L K : W.Modules)
    {U V : W.Opens} (h : V ≤ U)
    (b : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj K) :
    PullbackHomGluing.Construction.pullbackHomOnOpenEquiv L K V
        (ModuleHomTransport.Construction.moduleHomTransport U.ι b (W.homOfLE h) V.ι (W.homOfLE_ι h)) =
      (InternalHom.Construction.moduleInternalHom L K).presheaf.map (homOfLE h).op (PullbackHomGluing.Construction.pullbackHomOnOpenEquiv L K U b) := by
  have hm := pullbackHomOnImageEquiv_transport_eq (W.homOfLE h) U.ι L K b V.ι (W.homOfLE_ι h)
  have he := congrArg (Equiv.cast (congrArg
    (fun Q : W.Opens => (Γ(InternalHom.Construction.moduleInternalHom L K, Q) : Type u)) V.ι_image_top)) hm
  have hc := presheaf_section_cast_map (InternalHom.Construction.moduleInternalHom L K).presheaf U.ι_image_top V.ι_image_top
    (transportImageInclusion (W.homOfLE h) U.ι V.ι (W.homOfLE_ι h)) (homOfLE h)
      (pullbackHomOnImageEquiv U.ι L K b)
  exact he.trans hc

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PullbackHomRestriction
