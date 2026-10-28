import OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSeparation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.IntersectionMaps

/-! # Functions Gluing -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsGluing.CrystallineFunctionsGluing

noncomputable section

/-!
# Gluing actual ambient functions on native principal covers

Native compatibility on principal intersections is exactly compatibility
of fractions in the standard affine ring gluing theorem. Thus a unit-ideal
principal cover glues actual crystalline ambient functions uniquely.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)

local notation "QR" => Q.thickening.ring
local notation "Values" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSeparation.CrystallineFunctionsSeparation.values p k X

theorem principal_isSheafFor (s : Set QR) (hs : Ideal.span s = ⊤) :
    Presieve.IsSheafFor Values (CrystallinePrincipal.Covers.CrystallinePrincipalCovers.presieve p k X Q s Subtype.val) := by
  rw [CrystallinePrincipal.Covers.CrystallinePrincipalCovers.presieve, Presieve.isSheafFor_arrows_iff]
  intro z hz
  have hcompat : ∀ a b : s,
      IsLocalization.Away.awayToAwayRight (S := Localization.Away a.val) (P := Localization.Away (a.val * b.val)) a.val b.val (z a) =
        IsLocalization.Away.awayToAwayLeft (S := Localization.Away b.val) (P := Localization.Away (a.val * b.val)) b.val a.val (z b) := by
    intro a b
    have h := hz a b (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (a.val * b.val))
      (CrystallinePrincipal.IntersectionMaps.CrystallinePrincipalIntersectionMaps.left p k X Q a.val b.val)
      (CrystallinePrincipal.IntersectionMaps.CrystallinePrincipalIntersectionMaps.right p k X Q a.val b.val)
      (CrystallinePrincipal.IntersectionMaps.CrystallinePrincipalIntersectionMaps.condition p k X Q a.val b.val)
    exact (RingHom.congr_fun (CrystallinePrincipal.IntersectionMaps.CrystallinePrincipalIntersectionMaps.left_ambient p k X Q a.val b.val) (z a)).symm.trans
      (h.trans (RingHom.congr_fun (CrystallinePrincipal.IntersectionMaps.CrystallinePrincipalIntersectionMaps.right_ambient p k X Q a.val b.val) (z b)))
  change ∃! v : QR, ∀ a : s, algebraMap QR (Localization.Away a.val) v = z a
  exact Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs z hcompat

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsGluing.CrystallineFunctionsGluing
