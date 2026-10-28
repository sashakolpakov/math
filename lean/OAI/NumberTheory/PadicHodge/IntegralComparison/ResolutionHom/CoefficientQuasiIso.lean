import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.CoefficientEdge

/-! # Coefficient Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.CoefficientQuasiIso

noncomputable section

/-! For a coefficient injective resolution and a source complex whose
terms are acyclic for that coefficient, the actual coefficient edge into
the mixed Hom total is a quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (P : ChainComplex C ℕ)
  {Y : C} (I : InjectiveResolution Y)

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun J => (ModuleCat.hasColimitsOfSize.{z, t, 0, 0} R).has_colimits_of_shape (Discrete J)

local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Bicomplex.bicomplex R P I.cocomplex
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.CoefficientEdge.rowMap R P I.cocomplex I.ι

def columnIso (a : ℕ) : ((D).flip).X a ≅ InjectiveSectionCohomology.complex R (P.X a) I :=
  Iso.refl _

theorem augmented_column (a : ℕ) :
    (ShortComplex.mk ((e).f a) (((D).flip.X a).d 0 1)
      (CoefficientEdge.vertical R P I.cocomplex I.ι a)).Exact ∧ Mono ((e).f a) := by
  have h := Augmented.ResolutionCycles.augmentation_exact_and_mono I.cocomplex I.ι
  let : Mono (I.ι.f 0) := h.2
  let S := ShortComplex.mk (I.ι.f 0) (I.cocomplex.d 0 1)
    (Augmented.ResolutionCycles.augmentation_condition I.cocomplex I.ι)
  let : Mono S.f := h.2
  have hs : S.Exact := h.1
  exact ⟨IntegralComparison.Ext.ZeroKernels.map_exact R (P.X a) S hs,
    IntegralComparison.Ext.ZeroKernels.map_mono R (P.X a) (I.ι.f 0)⟩

variable (hP : ∀ a q, Subsingleton (Abelian.Ext.{z} (P.X a) Y (q + 1)))

include hP in
theorem column_exact (a q : ℕ) : ((D).flip.X a).ExactAt (q + 1) := by
  let : Subsingleton (Abelian.Ext.{z} (P.X a) Y (q + 1)) := hP a q
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (HomologicalComplex.homologyMapIso (columnIso R P I a) (q + 1) ≪≫
      InjectiveSectionCohomology.homologyIso R (P.X a) I (q + 1))

include hP in
theorem edge_quasiIso : QuasiIso (CoefficientEdge.edge R P I.cocomplex I.ι) := by
  let h := CoefficientEdge.horizontal R P I.cocomplex I.ι
  let w := CoefficientEdge.vertical R P I.cocomplex I.ι
  have he : QuasiIso ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (D).flip)
      (Acyclic.ChainCohomology.complex R Y P) (fun a => (e).f a) h w) :=
    Module.HorizontalTotal.Comparison.quasiIso R (D).flip
      (Acyclic.ChainCohomology.complex R Y P) (fun a => (e).f a) h w
      (fun a => (augmented_column R P I a).1) (fun a => (augmented_column R P I a).2)
      (column_exact R P I hP)
  have hf : QuasiIso ((D).totalFlipIso (.up ℕ)).hom := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := he) (hφ' := hf)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.CoefficientQuasiIso
