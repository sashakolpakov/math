import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Crystalline Restriction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.CrystallineRestriction.FramedCrystallineRestriction

noncomputable section

/-!
# Restricting lifted coordinates along crystalline morphisms

Any native morphism into a framed object uniquely acquires its restricted
coordinates. In particular, compatible families remain compatible after
forgetting coordinates, without assuming that native pullbacks exist.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u w

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a

def object (Q : Category.FramedCrystallineCategory.Object p k B σ a)
    {P : Site.Object p k X} (f : P ⟶ Q.base) :
    Category.FramedCrystallineCategory.Object p k B σ a where
  base := P
  coordinate i := f.ambientMap (Q.coordinate i)
  reduction_coordinate i := by
    rw [f.reduction_comm, Q.reduction_coordinate]
    exact (CrystallineFrame.Lifts.CrystallineFrameLifts.residual_naturality f (a i)).symm

def map (Q : Category.FramedCrystallineCategory.Object p k B σ a)
    {P : Site.Object p k X} (f : P ⟶ Q.base) : object p k B σ a Q f ⟶ Q :=
  ⟨f, fun _ => rfl⟩

def coneMap {Y₁ Y₂ Z : Category.FramedCrystallineCategory.Object p k B σ a}
    {P : Site.Object p k X} (f₁ : P ⟶ Y₁.base) (f₂ : P ⟶ Y₂.base)
    (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z) (h : f₁ ≫ g₁.hom = f₂ ≫ g₂.hom) :
    object p k B σ a Y₁ f₁ ⟶ Y₂ where
  hom := f₂
  coordinate_comm i := by
    have he := congrArg (fun f : P ⟶ Z.base => f.ambientMap (Z.coordinate i)) h
    change f₁.ambientMap (g₁.hom.ambientMap (Z.coordinate i)) =
      f₂.ambientMap (g₂.hom.ambientMap (Z.coordinate i)) at he
    rw [g₁.coordinate_comm, g₂.coordinate_comm] at he
    exact he.symm

theorem compatiblePreserving (J : GrothendieckTopology (Site.Object p k X)) :
    CompatiblePreserving.{w} J U where
  compatible := by
    intro ℱ Z T x hx Y₁ Y₂ P f₁ f₂ g₁ g₂ hg₁ hg₂ h
    exact hx (map p k B σ a _ f₁) (coneMap p k B σ a f₁ f₂ _ _ h) hg₁ hg₂
      (Category.FramedCrystallineCategory.hom_ext p k B σ a h)

def principal (Q : Category.FramedCrystallineCategory.Object p k B σ a) (s : Q.base.thickening.ring) :
    Category.FramedCrystallineCategory.Object p k B σ a :=
  object p k B σ a Q (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q.base s)

def principalProjection (Q : Category.FramedCrystallineCategory.Object p k B σ a) (s : Q.base.thickening.ring) :
    principal p k B σ a Q s ⟶ Q :=
  map p k B σ a Q (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q.base s)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.CrystallineRestriction.FramedCrystallineRestriction
