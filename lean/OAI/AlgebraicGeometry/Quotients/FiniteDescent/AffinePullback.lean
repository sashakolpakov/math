import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Affine Pullback -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffinePullback

noncomputable section

/-! Affine pullback and global sections, using the actual tilde adjunction.
The adjunction comparison is the generic construction also used in PoincareBundle. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

namespace Construction.AffinePullbackSections

private theorem paste {C : Type*} [Category* C]
    {A B D A' B' D' : C} {a : A ⟶ A'} {b : B ⟶ B'} {c : D ⟶ D'}
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : B ⟶ D} {g' : B' ⟶ D'}
    (h₁ : a ≫ f' = f ≫ b) (h₂ : b ≫ g' = g ≫ c) :
    a ≫ (f' ≫ g') = (f ≫ g) ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

private theorem map_square {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B A' B' : C} {a : A ⟶ A'} {b : B ⟶ B'} {f : A ⟶ B} {g : A' ⟶ B'}
    (h : a ≫ g = f ≫ b) : F.map a ≫ F.map g = F.map f ≫ F.map b := by
  rw [← F.map_comp, h, F.map_comp]

variable {R S : CommRingCat.{u}}

def sectionsFunctor (R : CommRingCat.{u}) :
    TopCat.Sheaf (ModuleCat R) (Spec R) ⥤ ModuleCat R :=
  TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)

def pushforwardSectionsIso (f : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars f.hom := by
  let e := pushforwardCompModulesSpecToSheafIso f
  let Γ := sectionsFunctor R
  refine NatIso.ofComponents (fun N => Γ.mapIso (e.app N)) ?_
  intro M N g
  exact congrArg (fun h => Γ.map h) (e.hom.naturality g)

def tildePullbackIso (f : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor S :=
  ((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
      (pushforwardSectionsIso f).symm)

def fromTildeIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    tilde ((moduleSpecΓFunctor (R := R)).obj M) ≅ M := by
  let a : tilde ((moduleSpecΓFunctor (R := R)).obj M) ⟶ M :=
    Scheme.Modules.fromTildeΓ (R := R) M
  have ha : IsIso a := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  exact @asIso _ _ _ _ a ha

def iso (f : R ⟶ S) (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars f.hom).obj ((moduleSpecΓFunctor (R := R)).obj M) ≅
      (moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map f)).obj M) :=
  tilde.toTildeΓNatIso.app _ ≪≫ (moduleSpecΓFunctor (R := S)).mapIso
    (((tildePullbackIso f).app _).symm ≪≫
      (Scheme.Modules.pullback (Spec.map f)).mapIso (fromTildeIso M))

theorem fromTildeIso_naturality {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) :
    (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map a) ≫ (fromTildeIso N).hom =
      (fromTildeIso M).hom ≫ a :=
  (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality a

theorem naturality (f : R ⟶ S) {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) :
    (ModuleCat.extendScalars f.hom).map ((moduleSpecΓFunctor (R := R)).map a) ≫ (iso f N).hom =
      (iso f M).hom ≫
        (moduleSpecΓFunctor (R := S)).map ((Scheme.Modules.pullback (Spec.map f)).map a) := by
  let b := (ModuleCat.extendScalars f.hom).map ((moduleSpecΓFunctor (R := R)).map a)
  have h₁ := (tilde.toTildeΓNatIso (R := S)).hom.naturality b
  have h₂ := (tildePullbackIso f).inv.naturality ((moduleSpecΓFunctor (R := R)).map a)
  have h₃ := fromTildeIso_naturality a
  simp only [Functor.comp_map, Functor.id_map] at h₁ h₂
  have hp := map_square (Scheme.Modules.pullback (Spec.map f)) h₃
  have hmiddle := paste h₂ hp
  exact paste h₁ (map_square (moduleSpecΓFunctor (R := S)) hmiddle)

end Construction.AffinePullbackSections

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffinePullback
