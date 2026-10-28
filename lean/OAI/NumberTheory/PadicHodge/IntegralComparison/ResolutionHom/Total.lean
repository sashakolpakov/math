import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.InjectiveRow
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.HorizontalTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

/-! # Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Total

noncomputable section

/-! The genuine mixed Hom total computes sections of an injective
coefficient resolution through its original source augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (P : ChainComplex C ℕ)
  {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε]
  (K : CochainComplex C ℕ)

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun I => (ModuleCat.hasColimitsOfSize.{z, t, 0, 0} R).has_colimits_of_shape (Discrete I)

def sections : CochainComplex (ModuleCat.{z} R) ℕ :=
  ((IntegralComparison.Ext.ModuleFunctor.functor R Z 0).mapHomologicalComplex (.up ℕ)).obj K

def total : CochainComplex (ModuleCat.{z} R) ℕ :=
  (Bicomplex.bicomplex R P K).total (.up ℕ)

def component (b : ℕ) : (sections R (Z := Z) K).X b ⟶
    ((Bicomplex.bicomplex R P K).X b).X 0 :=
  (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (K.X b) 0).map (ε.f 0).op

omit [QuasiIso ε] in
theorem vertical (b b' : ℕ) (_ : (ComplexShape.up ℕ).Rel b b') :
    component R P ε K b ≫ ((Bicomplex.bicomplex R P K).d b b').f 0 =
      (sections R (Z := Z) K).d b b' ≫ component R P ε K b' :=
  IntegralComparison.Ext.CoefficientNaturality.naturality R (K.d b b') 0 (ε.f 0).op

omit [QuasiIso ε] in
theorem horizontal (b : ℕ) : component R P ε K b ≫
    ((Bicomplex.bicomplex R P K).X b).d 0 1 = 0 := by
  have h := ((CochainComplex.fromSingle₀Equiv _ _)
    (InjectiveRow.augmentation R P ε (K.X b))).property
  change (InjectiveRow.augmentation R P ε (K.X b)).f 0 ≫ _ = 0 at h
  rw [InjectiveRow.augmentation_zero] at h
  exact h

def edge : sections R (Z := Z) K ⟶ Total.total R P K :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (Bicomplex.bicomplex R P K))
    (sections R K) (component R P ε K) (vertical R P ε K) (horizontal R P ε K)

variable (hK : ∀ b, Injective (K.X b))

include hK in
theorem augmented_row (b : ℕ) :
    (ShortComplex.mk (component R P ε K b)
      (((Bicomplex.bicomplex R P K).X b).d 0 1) (horizontal R P ε K b)).Exact ∧
        Mono (component R P ε K b) := by
  let : Injective (K.X b) := hK b
  let a := InjectiveRow.augmentation R P ε (K.X b)
  let : QuasiIso a := InjectiveRow.augmentation_quasiIso R P ε (K.X b)
  have h := Augmented.ResolutionCycles.augmentation_exact_and_mono
    (Acyclic.ChainCohomology.complex R (K.X b) P) a
  dsimp only [Augmented.ResolutionCycles.augmentation] at h
  have ha : a.f 0 = component R P ε K b :=
    InjectiveRow.augmentation_zero R P ε (K.X b)
  let S₀ := ShortComplex.mk (component R P ε K b)
    (((Bicomplex.bicomplex R P K).X b).d 0 1) (horizontal R P ε K b)
  let S₁ := ShortComplex.mk (a.f 0) ((Acyclic.ChainCohomology.complex R (K.X b) P).d 0 1)
    (Augmented.ResolutionCycles.augmentation_condition (Acyclic.ChainCohomology.complex R (K.X b) P) a)
  have e : S₀ ≅ S₁ :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (ha.trans (Category.comp_id _).symm))
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact (ShortComplex.exact_and_mono_f_iff_of_iso e).2 h

include hK in
theorem edge_quasiIso : QuasiIso (edge R P ε K) := by
  apply Module.HorizontalTotal.Comparison.quasiIso R
    (Bicomplex.bicomplex R P K) (sections R K)
    (component R P ε K) (vertical R P ε K) (horizontal R P ε K)
    (fun b => (augmented_row R P ε K hK b).1) (fun b => (augmented_row R P ε K hK b).2)
  intro b n
  let : Injective (K.X b) := hK b
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (InjectiveRow.positive_isZero R P ε (K.X b) n)

omit K hK in
def homologyIso {Y : C} (I : InjectiveResolution Y) (i : ℕ) :
    (Total.total R P I.cocomplex).homology i ≅ ModuleCat.of R (Abelian.Ext.{z} Z Y i) := by
  let : QuasiIso (edge R P ε I.cocomplex) := edge_quasiIso R P ε I.cocomplex I.injective
  exact (isoOfQuasiIsoAt (edge R P ε I.cocomplex) i).symm ≪≫
    InjectiveSectionCohomology.homologyIso R Z I i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Total
