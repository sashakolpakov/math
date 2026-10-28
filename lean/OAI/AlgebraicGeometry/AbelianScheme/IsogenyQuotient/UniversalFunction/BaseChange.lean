import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFunctions

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Universal global functions are invariant under actual Cartesian
recovery and arbitrary further base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A : Over S}

theorem GlobalFunctions.Construction.HasUniversalGlobalFunctions.isIso_of_isPullback
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A)
    {X T : Scheme.{u}} (a : X ⟶ A.left) (f : X ⟶ T) (b : T ⟶ S)
    (hp : IsPullback a f A.hom b) : IsIso f.appTop := by
  have : IsIso (pullback.snd A.hom b).appTop := hA T b
  have : IsIso hp.isoPullback.hom.appTop := Scheme.Γ.map_isIso hp.isoPullback.hom.op
  have he : f = hp.isoPullback.hom ≫ pullback.snd A.hom b := hp.isoPullback_hom_snd.symm
  rw [he, Scheme.Hom.comp_appTop]
  infer_instance

theorem GlobalFunctions.Construction.HasUniversalGlobalFunctions.pullback
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) {T : Scheme.{u}} (b : T ⟶ S) :
    GlobalFunctions.Construction.HasUniversalGlobalFunctions ((Over.pullback b).obj A) := by
  intro U c
  exact hA.isIso_of_isPullback
    (pullback.fst (pullback.snd A.hom b) c ≫ pullback.fst A.hom b)
    (pullback.snd (pullback.snd A.hom b) c) (c ≫ b)
    ((IsPullback.of_hasPullback (pullback.snd A.hom b) c).paste_horiz
      (IsPullback.of_hasPullback A.hom b))

theorem GlobalFunctions.Construction.HasUniversalGlobalFunctions.self (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) : IsIso A.hom.appTop :=
  hA.isIso_of_isPullback (𝟙 A.left) A.hom (𝟙 S) .of_id_fst

theorem GlobalFunctions.Construction.HasUniversalGlobalFunctions.of_isPullback
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A)
    {X T : Scheme.{u}} (a : X ⟶ A.left) (f : X ⟶ T) (b : T ⟶ S)
    (hp : IsPullback a f A.hom b) : GlobalFunctions.Construction.HasUniversalGlobalFunctions (Over.mk f) := by
  intro U c
  exact hA.isIso_of_isPullback (pullback.fst f c ≫ a) (pullback.snd f c) (c ≫ b)
    ((IsPullback.of_hasPullback f c).paste_horiz hp)

theorem GlobalFunctions.Construction.HasUniversalGlobalFunctions.restrict (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) (V : S.Opens) :
    IsIso (A.hom ∣_ V).appTop :=
  hA.isIso_of_isPullback (A.hom ⁻¹ᵁ V).ι (A.hom ∣_ V) V.ι (isPullback_morphismRestrict A.hom V).flip

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
