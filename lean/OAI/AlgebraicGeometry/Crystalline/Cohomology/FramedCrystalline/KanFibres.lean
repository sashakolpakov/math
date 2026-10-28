import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.CrystallineRestriction
import Mathlib.CategoryTheory.Limits.Final

/-! # Kan Fibres -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.KanFibres.FramedCrystallineKanFibres

noncomputable section

/-!
# The fibres computing extension from framed crystalline presheaves

Every arrow from a native object into a framed object pulls its coordinates
back uniquely. In the comma category for left Kan extension, the framings
of the fixed native object therefore form a final discrete subcategory.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a
local notation "Comma" => CostructuredArrow (Functor.op U) (op Q)

def Framings := {c : σ → Q.thickening.ring //
  ∀ i, Q.thickening.reduction (c i) =
    AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q (a i)}

def framed (c : Framings p k B σ a Q) : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a :=
  ⟨Q, c.val, c.property⟩

def inclusion : Discrete (Framings p k B σ a Q) ⥤ Comma :=
  Discrete.functor (fun c => CostructuredArrow.mk
    (Y := op (framed p k B σ a Q c)) (𝟙 (op Q)))

def pull (T : Comma) : Framings p k B σ a Q :=
  ⟨(CrystallineRestriction.FramedCrystallineRestriction.object p k B σ a T.left.unop T.hom.unop).coordinate,
    (CrystallineRestriction.FramedCrystallineRestriction.object p k B σ a T.left.unop T.hom.unop).reduction_coordinate⟩

theorem pull_eq {T S : Comma} (f : T ⟶ S) :
    pull p k B σ a Q T = pull p k B σ a Q S := by
  apply Subtype.ext
  funext i
  have h := congrArg Quiver.Hom.unop (CostructuredArrow.w f)
  change S.hom.unop ≫ f.left.unop.hom = T.hom.unop at h
  have he := congrArg (fun g : Q ⟶ T.left.unop.base =>
    g.ambientMap (T.left.unop.coordinate i)) h
  change S.hom.unop.ambientMap (f.left.unop.hom.ambientMap (T.left.unop.coordinate i)) =
    T.hom.unop.ambientMap (T.left.unop.coordinate i) at he
  rw [f.left.unop.coordinate_comm] at he
  exact he.symm

def retraction : Comma ⥤ Discrete (Framings p k B σ a Q) where
  obj T := Discrete.mk (pull p k B σ a Q T)
  map f := eqToHom (congrArg Discrete.mk (pull_eq p k B σ a Q f))

theorem underlying {T : Comma} {c : Discrete (Framings p k B σ a Q)}
    (f : T ⟶ (inclusion p k B σ a Q).obj c) :
    f.left.unop.hom = T.hom.unop := by
  have h := CostructuredArrow.w f
  change f.left.unop.hom.op ≫ 𝟙 (op Q) = T.hom at h
  have hh : f.left.unop.hom.op = T.hom :=
    (Category.comp_id f.left.unop.hom.op).symm.trans h
  exact congrArg Quiver.Hom.unop hh

instance hom_subsingleton (T : Comma) (c : Discrete (Framings p k B σ a Q)) :
    Subsingleton (T ⟶ (inclusion p k B σ a Q).obj c) where
  allEq f g := by
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply FramedCrystalline.Category.FramedCrystallineCategory.hom_ext p k B σ a
    exact (underlying p k B σ a Q f).trans (underlying p k B σ a Q g).symm

def lift (T : Comma) (c : Framings p k B σ a Q) (h : pull p k B σ a Q T = c) :
    T ⟶ (inclusion p k B σ a Q).obj (Discrete.mk c) := by
  let g : framed p k B σ a Q c ⟶ T.left.unop :=
    ⟨T.hom.unop, fun i => congrArg (fun c : Framings p k B σ a Q => c.val i) h⟩
  exact CostructuredArrow.homMk g.op (Category.comp_id _)

def homEquiv (T : Comma) (c : Discrete (Framings p k B σ a Q)) :
    ((retraction p k B σ a Q).obj T ⟶ c) ≃
      (T ⟶ (inclusion p k B σ a Q).obj c) where
  toFun f := lift p k B σ a Q T c.as (Discrete.eq_of_hom f)
  invFun f := eqToHom (congrArg Discrete.mk (by
    apply Subtype.ext
    funext i
    have h := f.left.unop.coordinate_comm i
    rw [underlying p k B σ a Q f] at h
    exact h))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def adjunction : retraction p k B σ a Q ⊣ inclusion p k B σ a Q :=
  Adjunction.mkOfHomEquiv
    { homEquiv := FramedCrystallineKanFibres.homEquiv p k B σ a Q
      homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
      homEquiv_naturality_right := fun _ _ => Subsingleton.elim _ _ }

instance inclusion_final : (inclusion p k B σ a Q).Final :=
  Functor.final_of_adjunction (adjunction p k B σ a Q)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.KanFibres.FramedCrystallineKanFibres
