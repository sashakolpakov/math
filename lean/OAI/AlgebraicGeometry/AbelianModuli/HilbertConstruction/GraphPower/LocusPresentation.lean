import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EnhancementParameterPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.GraphPowerEnhancementUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiFiniteQuasiProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ZeroNormalizedBundle

/-! # Locus Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation

noncomputable section

/-! Actual presentations of the graph-power enhancement locus. The
lifting criterion concerns every test scheme and the original marked
family with its zero-normalized projective line. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

structure GraphPowerLocusPresentation
    {R : Type} [CommRing R] (M : Over (Spec (.of R))) {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme) (d : ℕ) (δ : Fin g → ℕ) where
  parameter : Over (Spec (.of R))
  inclusion : parameter ⟶ M
  inclusion_left_mono : Mono inclusion.left
  inclusion_locallyOfFiniteType : LocallyOfFiniteType inclusion.left
  inclusion_quasiCompact : QuasiCompact inclusion.left
  lifts_iff : ∀ (T : Over (Spec (.of R))) (x : T ⟶ M),
    (∃ z : T ⟶ parameter, z ≫ inclusion = x) ↔
      Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback x.left)
        ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
          (pullback.fst F.abelian.scheme.hom x.left)) d)

attribute [instance] GraphPowerLocusPresentation.inclusion_left_mono
  GraphPowerLocusPresentation.inclusion_locallyOfFiniteType
  GraphPowerLocusPresentation.inclusion_quasiCompact

/-- A construction of the actual graph-power locus for every fixed
Noetherian projective full-level parameter family over the given base. -/
def GraphPowerLocusFactory (R : Type) [CommRing R]
    (g N d : ℕ) (δ : Fin g → ℕ) :=
  ∀ (M : Over (Spec (.of R))) [IsNoetherian M.left]
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme),
    GraphPowerLocusPresentation M F P d δ

namespace GraphPowerLocusPresentation
variable {R : Type} [CommRing R] {M : Over (Spec (.of R))} {g N d : ℕ}
    {δ : Fin g → ℕ} {F : Level.Data.AbelianSchemeWithFullLevel g N M.left}
    {P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme}
    (D : GraphPowerLocusPresentation M F P d δ)

instance inclusion_mono : Mono D.inclusion := Over.mono_of_mono_left _

theorem existsUnique_lift_iff (T : Over (Spec (.of R))) (x : T ⟶ M) :
    (∃! z : T ⟶ D.parameter, z ≫ D.inclusion = x) ↔
      Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback x.left)
        ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
          (pullback.fst F.abelian.scheme.hom x.left)) d) := by
  constructor
  · intro h
    exact (D.lifts_iff T x).mp h.exists
  · intro h
    obtain ⟨z, hz⟩ := (D.lifts_iff T x).mpr h
    exact ⟨z, hz, fun y hy => (cancel_mono D.inclusion).mp (hy.trans hz.symm)⟩

def quasiProjective [IsNoetherianRing R] (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation D.parameter :=
  Q.monomorphismSource D.inclusion

def universalEnhancement :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback D.inclusion.left)
      ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
        (pullback.fst F.abelian.scheme.hom D.inclusion.left)) d :=
  ((D.lifts_iff D.parameter D.inclusion).mp ⟨𝟙 _, Category.id_comp _⟩).some

def universalFamily : PolarizationData.PolarizedAbelianWithFullLevel g δ N D.parameter.left :=
  D.universalEnhancement.object

theorem universalFamily_abelian :
    D.universalFamily.abelian = F.abelian.pullback D.inclusion.left := rfl

theorem universalFamily_level :
    D.universalFamily.level = F.level.pullback D.inclusion.left := rfl

def universalPowerIso :
    ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
      (pullback.fst F.abelian.scheme.hom D.inclusion.left)).sheaf ≅
        (D.universalFamily.graphBundle.tensorPower d).sheaf :=
  D.universalEnhancement.powerIso.some

def enhancementAt {T : Over (Spec (.of R))} (z : T ⟶ D.parameter) :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback (z ≫ D.inclusion).left)
      ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
        (pullback.fst F.abelian.scheme.hom (z ≫ D.inclusion).left)) d := by
  let c : Over.mk (z ≫ D.inclusion).left ⟶ Over.mk D.inclusion.left := Over.homMk z.left rfl
  exact PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullback
    (F := F) (L := F.abelian.zeroNormalizedBundle P.ampleLineBundle)
    (T := Over.mk D.inclusion.left) (U := Over.mk (z ≫ D.inclusion).left)
    D.universalEnhancement c

def enhancementAtIso {T : Over (Spec (.of R))} (z : T ⟶ D.parameter) :
    Moduli.Isomorphisms.LevelPreservingIso (D.universalFamily.pullback z.left) (D.enhancementAt z).object := by
  let c : Over.mk (z ≫ D.inclusion).left ⟶ Over.mk D.inclusion.left := Over.homMk z.left rfl
  exact PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullbackModuliIso
    (F := F) (L := F.abelian.zeroNormalizedBundle P.ampleLineBundle)
    (T := Over.mk D.inclusion.left) (U := Over.mk (z ≫ D.inclusion).left)
    D.universalEnhancement c

theorem enhancementAt_class {T : Over (Spec (.of R))} (z : T ⟶ D.parameter) :
    (D.enhancementAt z).object.classOf = (D.universalFamily.pullback z.left).classOf :=
  (((D.universalFamily.pullback z.left).classOf_eq_iff (D.enhancementAt z).object).mpr
    ⟨D.enhancementAtIso z⟩).symm

theorem universalFamily_classifies [IsNoetherian M.left]
    (hd : 0 < d) (hδ : ∀ i, 0 < δ i)
    {T : Over (Spec (.of R))} (z : T ⟶ D.parameter)
    (E : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback (z ≫ D.inclusion).left)
      ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
        (pullback.fst F.abelian.scheme.hom (z ≫ D.inclusion).left)) d) :
    (D.universalFamily.pullback z.left).classOf = E.object.classOf := by
  apply (D.enhancementAt_class z).symm.trans
  exact Universal.GraphPowerEnhancementUniqueness.universalGraphPowerEnhancement_class_unique F.abelian P
    (Over.mk (z ≫ D.inclusion).left) (F.level.pullback (z ≫ D.inclusion).left)
    ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
      (pullback.fst F.abelian.scheme.hom (z ≫ D.inclusion).left))
    d (D.enhancementAt z) E hδ hd

end GraphPowerLocusPresentation

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation
