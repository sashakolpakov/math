import OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation

/-! # Open Cech Transport -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.OpenCechTransport

noncomputable section

/-!
# Transporting actual Čech complexes along open-domain identifications

A functor on open subsets which identifies the specified finite intersections
transports the actual Čech complexes of a presheaf. The construction preserves
the canonical section augmentation, including its map into the native total
complex. These are generic transport lemmas; their open-subspace hypotheses
are established separately for actual nested opens.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable (G : Opens Y ⥤ Opens X) (U : ι → Opens X) (V : ι → Opens Y)
variable (hUV : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
  G.obj (DeRham.Comparison.SmoothCech.cechIntersection V a) = DeRham.Comparison.SmoothCech.cechIntersection U a)

/-- Precomposition on the actual complex of module-valued presheaves. -/
abbrev cechPullbackPresheafComplex
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ) :
    CochainComplex ((Opens Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ :=
  (((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ (ModuleCat.{0} ℂ)).obj G.op).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K

variable (F : (Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ)

/-- The restriction square for identified open subsets commutes because
both composites are the same morphism of the open-set poset. -/
theorem openFunctor_restriction_square {A B : Opens Y} {C D : Opens X}
    (f : A ⟶ B) (g : C ⟶ D) (hA : G.obj A = C) (hB : G.obj B = D) :
    F.map g.op ≫ F.map (eqToHom hA).op =
      F.map (eqToHom hB).op ≫ F.map (G.map f).op := by
  rw [← F.map_comp, ← F.map_comp]
  congr 1

/-- The section families are identified by actual presheaf maps along
the equal open intersections. -/
def cechSpaceTransportDegreeEquiv (n : ℕ) :
    DeRham.Comparison.SmoothCech.CechCochain F U n ≃ₗ[ℂ] DeRham.Comparison.SmoothCech.CechCochain (G.op ⋙ F) V n :=
  LinearEquiv.piCongrRight (fun a =>
    (F.mapIso (eqToIso (hUV n a)).op).toLinearEquiv)

@[simp]
theorem cechSpaceTransportDegreeEquiv_apply (n : ℕ)
    (c : DeRham.Comparison.SmoothCech.CechCochain F U n) (a : Fin (n + 1) → ι) :
    cechSpaceTransportDegreeEquiv G U V hUV F n c a =
      F.map (eqToHom (hUV n a)).op (c a) := rfl

/-- The section-family identification preserves the actual alternating
Čech differential. -/
theorem cechSpaceTransportDegreeEquiv_d (n : ℕ) (c : DeRham.Comparison.SmoothCech.CechCochain F U n) :
    cechSpaceTransportDegreeEquiv G U V hUV F (n + 1) (DeRham.Comparison.SmoothCech.cechDelta F U n c) =
      DeRham.Comparison.SmoothCech.cechDelta (G.op ⋙ F) V n (cechSpaceTransportDegreeEquiv G U V hUV F n c) := by
  funext a
  rw [cechSpaceTransportDegreeEquiv_apply, DeRham.Comparison.SmoothCech.cechDelta_apply, DeRham.Comparison.SmoothCech.cechDelta_apply]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun x => ((-1 : ℤ) ^ j.val) • x)
  exact ConcreteCategory.congr_hom
    (openFunctor_restriction_square G F
      (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le_precomp V a j.succAbove))
      (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove))
      (hUV (n + 1) a) (hUV n (a ∘ j.succAbove))) (c (a ∘ j.succAbove))

/-- The actual Čech cochain complexes agree under the specified open
intersection identifications. -/
def cechSpaceTransportIso : DeRham.Comparison.SmoothCech.cechComplex F U ≅ DeRham.Comparison.SmoothCech.cechComplex (G.op ⋙ F) V :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cechSpaceTransportDegreeEquiv G U V hUV F n).toModuleIso) (by
      intro i j hij
      obtain rfl : i + 1 = j := hij
      rw [DeRham.Comparison.SmoothCech.cechComplex_d, DeRham.Comparison.SmoothCech.cechComplex_d]
      apply ConcreteCategory.ext_apply
      intro c
      exact (cechSpaceTransportDegreeEquiv_d G U V hUV F i c).symm)

/-- The Čech identification is natural in the actual coefficient presheaf. -/
def cechSpaceTransportNatIso :
    DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor U ≅
      (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ (ModuleCat.{0} ℂ)).obj G.op ⋙
        DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor V :=
  NatIso.ofComponents (fun F => cechSpaceTransportIso G U V hUV F) (by
    intro F F' α
    apply HomologicalComplex.Hom.ext
    funext n
    apply ConcreteCategory.ext_apply
    intro c
    funext a
    exact ConcreteCategory.congr_hom
      (α.naturality (eqToHom (hUV n a)).op).symm (c a))

variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ)

/-- The Čech row identification lifts to the actual coefficient double
complex, preserving both differentials. -/
def cechSpaceTransportDoubleIso :
    DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex U K ≅ DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex V (cechPullbackPresheafComplex G K) :=
  (HomologicalComplex₂.flipFunctor (ModuleCat.{0} ℂ)
    (ComplexShape.up ℕ) (ComplexShape.up ℕ)).mapIso
      ((NatIso.mapHomologicalComplex (cechSpaceTransportNatIso G U V hUV)
        (ComplexShape.up ℕ)).app K)

@[simp]
theorem cechSpaceTransportDoubleIso_hom_f_f (p q : ℕ) :
    ((cechSpaceTransportDoubleIso G U V hUV K).hom.f p).f q =
      ModuleCat.ofHom (cechSpaceTransportDegreeEquiv G U V hUV (K.X q) p).toLinearMap := rfl

/-- The induced isomorphism of the native signed total complexes. -/
def cechSpaceTransportTotalIso :
    DeRham.Comparison.CechTotalFunctor.cechTotalComplex U K ≅ DeRham.Comparison.CechTotalFunctor.cechTotalComplex V (cechPullbackPresheafComplex G K) :=
  (HomologicalComplex₂.totalFunctor (ModuleCat.{0} ℂ)
    (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)).mapIso
      (cechSpaceTransportDoubleIso G U V hUV K)

/-- The total isomorphism acts by the proved section-family identification
on each summand. -/
theorem cechSpaceTransportTotalIso_inclusion (p q n : ℕ) (h : p + q = n) :
    DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U K p q n h ≫ (cechSpaceTransportTotalIso G U V hUV K).hom.f n =
      ModuleCat.ofHom (cechSpaceTransportDegreeEquiv G U V hUV (K.X q) p).toLinearMap ≫
        DeRham.Comparison.CechTotalFunctor.cechTotalInclusion V (cechPullbackPresheafComplex G K) p q n h :=
  HomologicalComplex₂.ιTotal_map (K := DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex U K)
    (L := DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex V (cechPullbackPresheafComplex G K))
    (φ := (cechSpaceTransportDoubleIso G U V hUV K).hom)
    (c₁₂ := ComplexShape.up ℕ) p q n h

variable (W : Opens X) (T : Opens Y) (hWT : G.obj T = W)
variable (hU : ∀ i, U i ≤ W) (hV : ∀ i, V i ≤ T)

/-- Actual section complexes on corresponding domains are identified by
their presheaf maps along the equality of those domains. -/
def cechSpaceTransportSectionsIso :
    DeRham.Comparison.CechComplexAugmentation.presheafComplexSections W K ≅
      DeRham.Comparison.CechComplexAugmentation.presheafComplexSections T (cechPullbackPresheafComplex G K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (K.X q).mapIso (eqToIso hWT).op) (by
      intro i j _
      exact (K.d i j).naturality (eqToHom hWT).op)

/-- The column augmentations agree under the actual section identifications. -/
theorem cechSpaceTransport_column :
    (cechSpaceTransportSectionsIso G K W T hWT).hom ≫
        DeRham.Comparison.CechComplexAugmentation.cechColumnAugmentation V T hV (cechPullbackPresheafComplex G K) =
      DeRham.Comparison.CechComplexAugmentation.cechColumnAugmentation U W hU K ≫
        (cechSpaceTransportDoubleIso G U V hUV K).hom.f 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ConcreteCategory.ext_apply
  intro s
  funext a
  exact (ConcreteCategory.congr_hom
    (openFunctor_restriction_square G (K.X q)
      (homOfLE (DeRham.Comparison.CechComplexAugmentation.cechIntersection_le_openDomain V T hV a))
      (homOfLE (DeRham.Comparison.CechComplexAugmentation.cechIntersection_le_openDomain U W hU a))
      (hUV 0 a) hWT) s).symm

/-- The square of the actual total augmentations commutes. -/
theorem cechSpaceTransport_augmentation :
    (cechSpaceTransportSectionsIso G K W T hWT).hom ≫
        DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation V T hV (cechPullbackPresheafComplex G K) =
      DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U W hU K ≫
        (cechSpaceTransportTotalIso G U V hUV K).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  have hc := congrArg (fun f => f.f q)
    (cechSpaceTransport_column G U V hUV K W T hWT hU hV)
  simp only [HomologicalComplex.comp_f, cechSpaceTransportDoubleIso_hom_f_f] at hc
  have hi := cechSpaceTransportTotalIso_inclusion G U V hUV K 0 q q (Nat.zero_add q)
  simp only [HomologicalComplex.comp_f, DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation_f]
  rw [← Category.assoc, hc, Category.assoc, ← hi, ← Category.assoc]

/-- Corresponding canonical augmentations are isomorphic as arrows of
complexes, not just on their cohomology objects. -/
def cechSpaceTransportAugmentationArrowIso :
    Arrow.mk (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U W hU K) ≅
      Arrow.mk (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation V T hV (cechPullbackPresheafComplex G K)) :=
  Arrow.isoMk (cechSpaceTransportSectionsIso G K W T hWT)
    (cechSpaceTransportTotalIso G U V hUV K)
    (cechSpaceTransport_augmentation G U V hUV K W T hWT hU hV)

include hUV hWT in
/-- Quasi-isomorphism of canonical augmentations is invariant under the
proved open-domain transport. -/
theorem cechSpaceTransport_augmentation_quasiIso_iff :
    QuasiIso (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U W hU K) ↔
      QuasiIso (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation V T hV (cechPullbackPresheafComplex G K)) :=
  quasiIso_iff_of_arrow_mk_iso _ _
    (cechSpaceTransportAugmentationArrowIso G U V hUV K W T hWT hU hV)

end

end OAI.AlgebraicTopology.Cohomology.Singular.OpenCechTransport
