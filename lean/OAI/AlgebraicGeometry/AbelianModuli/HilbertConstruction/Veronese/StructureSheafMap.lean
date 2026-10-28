import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveComap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogeneousLocalRingMap

/-! # Structure Sheaf Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.StructureSheafMap

noncomputable section

/-! Restriction of homogeneous primes and fractions defines the map
of structure sheaves for the Veronese comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization _root_.TopologicalSpace
open ProjectiveSpectrum.StructureSheaf
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ) [NeZero N]

def veroneseHomogeneousStalkMap (p : ProjectiveSpectrum g) :
    HomogeneousLocalization.AtPrime (Grading.veroneseGrading g N)
        (ProjectiveComap.veroneseProjectiveComap g N p).asHomogeneousIdeal.toIdeal →+*
      HomogeneousLocalization.AtPrime g p.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalRingMap.regradedHomogeneousLocalRingMap (Grading.veroneseGrading g N) g (N * ·)
    (Subalgebra.veroneseSubalgebra g N).val.toRingHom (fun _ _ hx => hx) _ _ rfl

instance veroneseHomogeneousStalkMap_isLocalHom (p : ProjectiveSpectrum g) :
    IsLocalHom (veroneseHomogeneousStalkMap g N p) :=
  HomogeneousLocalRingMap.regradedHomogeneousLocalRingMap_isLocalHom _ _ _ _ _ _ _ _

def veroneseComapStructureSheafFun
    (U : Opens (ProjectiveSpectrum (Grading.veroneseGrading g N))) (V : Opens (ProjectiveSpectrum g))
    (hUV : V.1 ⊆ ProjectiveComap.veroneseProjectiveContinuousMap g N ⁻¹' U.1)
    (s : ∀ x : U, HomogeneousLocalization.AtPrime (Grading.veroneseGrading g N) x.val.asHomogeneousIdeal.toIdeal)
    (y : V) : HomogeneousLocalization.AtPrime g y.val.asHomogeneousIdeal.toIdeal :=
  veroneseHomogeneousStalkMap g N y.val (s ⟨ProjectiveComap.veroneseProjectiveComap g N y.val, hUV y.property⟩)

theorem veronese_isLocallyFraction_comap
    (U : Opens (ProjectiveSpectrum (Grading.veroneseGrading g N))) (V : Opens (ProjectiveSpectrum g))
    (hUV : V.1 ⊆ ProjectiveComap.veroneseProjectiveContinuousMap g N ⁻¹' U.1)
    (s : ∀ x : U, HomogeneousLocalization.AtPrime (Grading.veroneseGrading g N) x.val.asHomogeneousIdeal.toIdeal)
    (hs : (isLocallyFraction (Grading.veroneseGrading g N)).pred s) :
    (isLocallyFraction g).pred (veroneseComapStructureSheafFun g N U V hUV s) := by
  rintro ⟨p, hpV⟩
  obtain ⟨W, hpW, iWU, d, a, b, hb, hfrac⟩ := hs ⟨ProjectiveComap.veroneseProjectiveComap g N p, hUV hpV⟩
  refine ⟨W.comap (ProjectiveComap.veroneseProjectiveContinuousMap g N) ⊓ V, ⟨hpW, hpV⟩,
    Opens.infLERight _ _, N * d, ⟨a.val.val, a.property⟩, ⟨b.val.val, b.property⟩,
    (fun ⟨q, hqW, _⟩ => hb ⟨ProjectiveComap.veroneseProjectiveComap g N q, hqW⟩), ?_⟩
  rintro ⟨q, hqW, hqV⟩
  unfold veroneseComapStructureSheafFun
  change veroneseHomogeneousStalkMap g N q
    (s (iWU ⟨ProjectiveComap.veroneseProjectiveComap g N q, hqW⟩)) = _
  exact congrArg (veroneseHomogeneousStalkMap g N q)
    (hfrac ⟨ProjectiveComap.veroneseProjectiveComap g N q, hqW⟩)

def veroneseComapStructureSheaf
    (U : Opens (ProjectiveSpectrum (Grading.veroneseGrading g N))) (V : Opens (ProjectiveSpectrum g))
    (hUV : V.1 ⊆ ProjectiveComap.veroneseProjectiveContinuousMap g N ⁻¹' U.1) :
    (ProjectiveSpectrum.Proj.structureSheaf (Grading.veroneseGrading g N)).1.obj (.op U) →+* (ProjectiveSpectrum.Proj.structureSheaf g).1.obj (.op V) where
  toFun s := ⟨veroneseComapStructureSheafFun g N U V hUV s.val,
    veronese_isLocallyFraction_comap g N U V hUV s.val s.property⟩
  map_one' := Subtype.ext (funext fun y => map_one (veroneseHomogeneousStalkMap g N y.val))
  map_zero' := Subtype.ext (funext fun y => map_zero (veroneseHomogeneousStalkMap g N y.val))
  map_add' _s _t := Subtype.ext (funext fun y => map_add (veroneseHomogeneousStalkMap g N y.val) _ _)
  map_mul' _s _t := Subtype.ext (funext fun y => map_mul (veroneseHomogeneousStalkMap g N y.val) _ _)

def veroneseSheafedSpaceMap :
    Proj.toSheafedSpace g ⟶ Proj.toSheafedSpace (Grading.veroneseGrading g N) where
  hom := {
    base := TopCat.ofHom (ProjectiveComap.veroneseProjectiveContinuousMap g N)
    c := { app U := CommRingCat.ofHom (veroneseComapStructureSheaf g N _ _ Set.Subset.rfl) } }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.StructureSheafMap
