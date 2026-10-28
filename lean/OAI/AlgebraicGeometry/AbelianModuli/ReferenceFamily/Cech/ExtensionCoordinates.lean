import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleCycleSequence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitExtensionCoherence
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ShortExactPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

/-! # Extension Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates

noncomputable section

section

/-! A degree-one Cech cocycle gives an actual algebraic extension of the
structure module by itself. Algebraic splitting is a literal Cech lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)
    (c : HilbertConstruction.Line.Bundles.structureModule X ⟶ ModuleCycleSequence.cechModuleOneCycles X U)

def cechCocycleExtension : ShortComplex X.Modules :=
  ArithmeticGeometry.OrdinaryLocus.Openness.ShortExactPullback.Construction.pullbackShortComplex (ModuleCycleSequence.cechModuleCycleSequence X U) c

theorem cechCocycleExtension_shortExact (hU : iSup U = ⊤) :
    (cechCocycleExtension X U c).ShortExact :=
  ArithmeticGeometry.OrdinaryLocus.Openness.ShortExactPullback.Construction.pullbackShortComplex_shortExact (ModuleCycleSequence.cechModuleCycleSequence X U) c
    (ModuleCycleSequence.cechModuleCycleSequence_shortExact X U hU)

theorem cechCocycleExtension_coherent (hU : iSup U = ⊤) :
    (cechCocycleExtension X U c).X₂.IsQuasicoherent ∧ (cechCocycleExtension X U c).X₂.IsFiniteType :=
  UnitExtensionCoherence.unitExtension_coherent _ (cechCocycleExtension X U c).f (cechCocycleExtension X U c).g
    (cechCocycleExtension X U c).zero (cechCocycleExtension_shortExact X U c hU)

theorem cechCocycleExtension_lift_of_splitting (s : (cechCocycleExtension X U c).Splitting) :
    ∃ t : HilbertConstruction.Line.Bundles.structureModule X ⟶ TermModules.cechTermModule X U 0, t ≫ ModuleCycleSequence.cechModuleToOneCycles X U = c := by
  let a : HilbertConstruction.Line.Bundles.structureModule X ⟶ pullback (ModuleCycleSequence.cechModuleToOneCycles X U) c := s.s
  have ha : a ≫ pullback.snd (ModuleCycleSequence.cechModuleToOneCycles X U) c = 𝟙 _ := s.s_g
  refine ⟨a ≫ pullback.fst (ModuleCycleSequence.cechModuleToOneCycles X U) c, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  rw [ha, Category.id_comp]

theorem cechCocycleExtension_splitting_of_lift (hU : iSup U = ⊤)
    (t : HilbertConstruction.Line.Bundles.structureModule X ⟶ TermModules.cechTermModule X U 0) (ht : t ≫ ModuleCycleSequence.cechModuleToOneCycles X U = c) :
    Nonempty (cechCocycleExtension X U c).Splitting := by
  let s := pullback.lift t (𝟙 (HilbertConstruction.Line.Bundles.structureModule X)) (ht.trans (Category.id_comp c).symm)
  have hs : s ≫ (cechCocycleExtension X U c).g = 𝟙 _ := pullback.lift_snd _ _ _
  have hS := cechCocycleExtension_shortExact X U c hU
  exact ⟨ShortComplex.Splitting.ofExactOfSection _ hS.exact s hs hS.mono_f⟩

theorem cechCocycleExtension_split_iff_lift (hU : iSup U = ⊤) :
    Nonempty (cechCocycleExtension X U c).Splitting ↔
      ∃ t : HilbertConstruction.Line.Bundles.structureModule X ⟶ TermModules.cechTermModule X U 0, t ≫ ModuleCycleSequence.cechModuleToOneCycles X U = c := by
  constructor
  · rintro ⟨s⟩
    exact cechCocycleExtension_lift_of_splitting X U c s
  · rintro ⟨t, ht⟩
    exact cechCocycleExtension_splitting_of_lift X U c hU t ht

end

section

/-! Literal global degree-one Cech cocycles define the constructed
extension, and its splitting recovers a literal algebraic coboundary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)
    (c : Γ(TermModules.cechTermModule X U 1, ⊤)) (hc : (ModuleDifferential.cechModuleDifferential X U 1).app ⊤ c = 0)

def cechOneCycleHom : HilbertConstruction.Line.Bundles.structureModule X ⟶ ModuleCycleSequence.cechModuleOneCycles X U := by
  let s := (HilbertConstruction.Global.Sections.moduleSectionHomEquiv (TermModules.cechTermModule X U 1)).symm c
  apply kernel.lift (ModuleDifferential.cechModuleDifferential X U 1) s
  apply (HilbertConstruction.Global.Sections.moduleSectionHomEquiv (TermModules.cechTermModule X U 2)).injective
  change (ModuleDifferential.cechModuleDifferential X U 1).app ⊤ (s.app ⊤ (1 : Γ(X, ⊤))) = 0
  have hs : s.app ⊤ (1 : Γ(X, ⊤)) = c :=
    (HilbertConstruction.Global.Sections.moduleSectionHomEquiv (TermModules.cechTermModule X U 1)).apply_symm_apply c
  rw [hs]
  exact hc

theorem cechOneCycleHom_ι :
    cechOneCycleHom X U c hc ≫ kernel.ι (ModuleDifferential.cechModuleDifferential X U 1) =
      (HilbertConstruction.Global.Sections.moduleSectionHomEquiv (TermModules.cechTermModule X U 1)).symm c :=
  kernel.lift_ι _ _ _

theorem cechOneCycleHom_value :
    (cechOneCycleHom X U c hc ≫ kernel.ι (ModuleDifferential.cechModuleDifferential X U 1)).app ⊤ (1 : Γ(X, ⊤)) = c := by
  exact (congrArg (fun f => f.app ⊤ (1 : Γ(X, ⊤))) (cechOneCycleHom_ι X U c hc)).trans
    ((HilbertConstruction.Global.Sections.moduleSectionHomEquiv (TermModules.cechTermModule X U 1)).apply_symm_apply c)

theorem cechOneCycle_boundary_of_lift
    (t : HilbertConstruction.Line.Bundles.structureModule X ⟶ TermModules.cechTermModule X U 0)
    (ht : t ≫ ModuleCycleSequence.cechModuleToOneCycles X U = cechOneCycleHom X U c hc) :
    ∃ b : Γ(TermModules.cechTermModule X U 0, ⊤), (ModuleDifferential.cechModuleDifferential X U 0).app ⊤ b = c := by
  have hq : ModuleCycleSequence.cechModuleToOneCycles X U ≫ kernel.ι (ModuleDifferential.cechModuleDifferential X U 1) =
      ModuleDifferential.cechModuleDifferential X U 0 := kernel.lift_ι _ _ _
  have he : t ≫ ModuleDifferential.cechModuleDifferential X U 0 =
      cechOneCycleHom X U c hc ≫ kernel.ι (ModuleDifferential.cechModuleDifferential X U 1) :=
    (congrArg (t ≫ ·) hq).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ kernel.ι (ModuleDifferential.cechModuleDifferential X U 1)) ht))
  exact ⟨t.app ⊤ (1 : Γ(X, ⊤)),
    (congrArg (fun f => f.app ⊤ (1 : Γ(X, ⊤))) he).trans (cechOneCycleHom_value X U c hc)⟩

theorem cechOneCycle_boundary_of_extension_splitting
    (s : (cechCocycleExtension X U (cechOneCycleHom X U c hc)).Splitting) :
    ∃ b : Γ(TermModules.cechTermModule X U 0, ⊤), (ModuleDifferential.cechModuleDifferential X U 0).app ⊤ b = c := by
  obtain ⟨t, ht⟩ := cechCocycleExtension_lift_of_splitting X U (cechOneCycleHom X U c hc) s
  exact cechOneCycle_boundary_of_lift X U c hc t ht

end

section

/-! A native holomorphic scalar retraction of the constructed cocycle
extension gives a literal algebraic Cech coboundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem unitExtension_splitting_of_holomorphicScalarRetraction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (M : V.carrier.Modules) (i : HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ M)
    (p : M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact) (r : Holomorphic.FunctionalNe.HolomorphicScalarFunctional V M)
    (hr : i ≫ r = Holomorphic.FunctionalDescent.nativeStructureEvaluation V) :
    Nonempty (ShortComplex.mk i p hip).Splitting := by
  have hcoh := UnitExtensionCoherence.unitExtension_coherent M i p hip hS
  let : M.IsQuasicoherent := hcoh.1
  let : M.IsFiniteType := hcoh.2
  obtain ⟨g, hg⟩ := CoherentScalarAlgebraization.coherent_holomorphicScalarFunctional_algebraic V M r
  have hgr : g ≫ Holomorphic.FunctionalDescent.nativeStructureEvaluation V = r := hg
  have hgi : i ≫ g = 𝟙 _ := by
    apply Holomorphic.FunctionalDescent.holomorphicScalarFunctionalOfAlgebraic_injective V (HilbertConstruction.Line.Bundles.structureModule V.carrier)
    exact (Category.assoc _ _ _).trans
      ((congrArg (i ≫ ·) hgr).trans (hr.trans (Category.id_comp _).symm))
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction (ShortComplex.mk i p hip)
    hS.exact g hgi hS.epi_g⟩

theorem cechOneCycle_boundary_of_holomorphicScalarRetraction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {I : Type} (U : I → V.carrier.Opens) (hU : iSup U = ⊤)
    (c : Γ(TermModules.cechTermModule V.carrier U 1, ⊤))
    (hc : (ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ c = 0)
    (r : Holomorphic.FunctionalNe.HolomorphicScalarFunctional V (cechCocycleExtension V.carrier U
      (cechOneCycleHom V.carrier U c hc)).X₂)
    (hr : (cechCocycleExtension V.carrier U (cechOneCycleHom V.carrier U c hc)).f ≫ r =
      Holomorphic.FunctionalDescent.nativeStructureEvaluation V) :
    ∃ b : Γ(TermModules.cechTermModule V.carrier U 0, ⊤),
      (ModuleDifferential.cechModuleDifferential V.carrier U 0).app ⊤ b = c := by
  let S := cechCocycleExtension V.carrier U (cechOneCycleHom V.carrier U c hc)
  have hS : S.ShortExact := cechCocycleExtension_shortExact V.carrier U _ hU
  obtain ⟨s⟩ := unitExtension_splitting_of_holomorphicScalarRetraction V S.X₂ S.f S.g S.zero hS r hr
  exact cechOneCycle_boundary_of_extension_splitting V.carrier U c hc s

end

section

/-! The actual cocycle extension retains its zero-cochain projection and
the literal local equation relating its two coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem moduleSectionHomEquiv_symm_on_open {X : Scheme.{0}} (M : X.Modules)
    (c : Γ(M, ⊤)) (W : X.Opens) (a : Γ(X, W)) :
    ((HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm c).app W a = a • M.presheaf.map W.leTop.op c := by
  let s := (HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm c
  have h1 : s.app W (1 : Γ(X, W)) = M.presheaf.map W.leTop.op c :=
    (HilbertConstruction.Section.Gluing.moduleSectionHomEquiv_restrict M s W).symm.trans
      (congrArg (M.presheaf.map W.leTop.op) ((HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).apply_symm_apply c))
  have h := (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp s W).map_smul a (1 : Γ(X, W))
  change s.app W (show Γ(X, W) from a * 1) = a • s.app W (1 : Γ(X, W)) at h
  exact (congrArg (fun b : Γ(X, W) => s.app W b) (mul_one a)).symm.trans
    (h.trans (congrArg (a • ·) h1))

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)
    (c : HilbertConstruction.Line.Bundles.structureModule X ⟶ ModuleCycleSequence.cechModuleOneCycles X U)

def cechCocycleZeroProjection : (cechCocycleExtension X U c).X₂ ⟶ TermModules.cechTermModule X U 0 :=
  pullback.fst (ModuleCycleSequence.cechModuleToOneCycles X U) c

theorem cechCocycleZeroProjection_inclusion :
    (cechCocycleExtension X U c).f ≫ cechCocycleZeroProjection X U c = ModuleAugmentation.cechModuleAugmentation X U :=
  pullback.lift_fst _ _ _

theorem cechCocycleZeroProjection_differential :
    cechCocycleZeroProjection X U c ≫ ModuleDifferential.cechModuleDifferential X U 0 =
      (cechCocycleExtension X U c).g ≫ c ≫ kernel.ι (ModuleDifferential.cechModuleDifferential X U 1) := by
  have hq : ModuleCycleSequence.cechModuleToOneCycles X U ≫ kernel.ι (ModuleDifferential.cechModuleDifferential X U 1) =
      ModuleDifferential.cechModuleDifferential X U 0 := kernel.lift_ι _ _ _
  exact (congrArg (cechCocycleZeroProjection X U c ≫ ·) hq).symm.trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ kernel.ι (ModuleDifferential.cechModuleDifferential X U 1)) (pullback.condition
        (f := ModuleCycleSequence.cechModuleToOneCycles X U) (g := c))).trans (Category.assoc _ _ _)))

variable (z : Γ(TermModules.cechTermModule X U 1, ⊤)) (hz : (ModuleDifferential.cechModuleDifferential X U 1).app ⊤ z = 0)

theorem cechOneCycleZeroProjection_differential :
    cechCocycleZeroProjection X U (cechOneCycleHom X U z hz) ≫ ModuleDifferential.cechModuleDifferential X U 0 =
      (cechCocycleExtension X U (cechOneCycleHom X U z hz)).g ≫
        (HilbertConstruction.Global.Sections.moduleSectionHomEquiv (TermModules.cechTermModule X U 1)).symm z :=
  (cechCocycleZeroProjection_differential X U (cechOneCycleHom X U z hz)).trans
    (congrArg ((cechCocycleExtension X U (cechOneCycleHom X U z hz)).g ≫ ·) (cechOneCycleHom_ι X U z hz))

theorem cechOneCycle_local_equation (W : X.Opens)
    (m : Γ((cechCocycleExtension X U (cechOneCycleHom X U z hz)).X₂, W)) :
    (ModuleDifferential.cechModuleDifferential X U 0).app W
      ((cechCocycleZeroProjection X U (cechOneCycleHom X U z hz)).app W m) =
      (show Γ(X, W) from (cechCocycleExtension X U (cechOneCycleHom X U z hz)).g.app W m) •
        (TermModules.cechTermModule X U 1).presheaf.map W.leTop.op z := by
  exact (congrArg (fun f => f.app W m) (cechOneCycleZeroProjection_differential X U z hz)).trans
    (moduleSectionHomEquiv_symm_on_open (TermModules.cechTermModule X U 1) z W _)

end

section

/-! Literal regular coefficients of the original Cech module terms and
their scalar, restriction, and differential formulas. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.TopCat.Sheaf

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)

def cechIntersection (n : ℕ) (i : Fin (n + 1) → I) : X.Opens := ∏ᶜ fun k => U (i k)

def cechCoefficient (n : ℕ) (W : X.Opens) (c : Γ(TermModules.cechTermModule X U n, W)) (i : Fin (n + 1) → I) :
    Γ(X, W ⊓ cechIntersection U n i) :=
  SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U n W c i

theorem cechCoefficient_add (n : ℕ) (W : X.Opens) (c d : Γ(TermModules.cechTermModule X U n, W))
    (i : Fin (n + 1) → I) :
    cechCoefficient U n W (c + d) i = cechCoefficient U n W c i + cechCoefficient U n W d i :=
  congrArg (fun a => a i) ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U n W).map_add c d)

theorem cechCoefficient_smul (n : ℕ) (W : X.Opens) (a : Γ(X, W))
    (c : Γ(TermModules.cechTermModule X U n, W)) (i : Fin (n + 1) → I) :
    cechCoefficient U n W (a • c) i =
      X.presheaf.map (homOfLE (show W ⊓ cechIntersection U n i ≤ W from inf_le_left)).op a *
        cechCoefficient U n W c i :=
  TermModules.cechTermCoordinates_smul X U n W a c i

theorem cechCoefficient_restrict (n : ℕ) {V W : X.Opens} (h : W ≤ V)
    (c : Γ(TermModules.cechTermModule X U n, V)) (i : Fin (n + 1) → I) :
    cechCoefficient U n W ((TermModules.cechTermModule X U n).presheaf.map (homOfLE h).op c) i =
      X.presheaf.map (homOfLE (inf_le_inf_right (cechIntersection U n i) h)).op
        (cechCoefficient U n V c i) :=
  TermRestriction.cechTermCoordinates_restrict (TermModules.structureAbelianSheaf X) U n h c i

def cechFaceIndex (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 2) → I) : Fin (n + 1) → I :=
  i ∘ (SimplexCategory.δ k).toOrderHom.toFun

theorem cechIntersection_le_face (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 2) → I) :
    cechIntersection U (n + 1) i ≤ cechIntersection U n (cechFaceIndex n k i) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i)

theorem cechCoefficient_differential (n : ℕ) (W : X.Opens) (c : Γ(TermModules.cechTermModule X U n, W))
    (i : Fin (n + 2) → I) :
    cechCoefficient U (n + 1) W ((ModuleDifferential.cechModuleDifferential X U n).app W c) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        X.presheaf.map (homOfLE (inf_le_inf_left W (cechIntersection_le_face U n k i))).op
          (cechCoefficient U n W c (cechFaceIndex n k i)) := by
  have he := congrArg (fun f => f.hom.app (op W) c) (ModuleDifferential.cechModuleDifferential_underlying X U n)
  exact (congrArg (fun a => cechCoefficient U (n + 1) W a i) he).trans
    (SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechDifferential_apply (TermModules.structureAbelianSheaf X) U n W c i)

end

/-! Regular coefficients on the actual Cech intersections act on
the original Cech module sheaf, compatibly with all open restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.TopCat.Sheaf

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens) (n : ℕ)
    (r : ∀ i : Fin (n + 1) → I, Γ(X, cechIntersection U n i))

def cechMultiplySections (W : X.Opens) (a : Γ(TermModules.cechTermModule X U n, W)) :
    Γ(TermModules.cechTermModule X U n, W) :=
  (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U n W).symm
    (fun i => X.presheaf.map (homOfLE (show W ⊓ cechIntersection U n i ≤ cechIntersection U n i
      from inf_le_right)).op (r i) * cechCoefficient U n W a i)

theorem cechMultiplySections_coefficient (W : X.Opens) (a : Γ(TermModules.cechTermModule X U n, W))
    (i : Fin (n + 1) → I) :
    cechCoefficient U n W (cechMultiplySections U n r W a) i =
      X.presheaf.map (homOfLE (show W ⊓ cechIntersection U n i ≤ cechIntersection U n i
        from inf_le_right)).op (r i) * cechCoefficient U n W a i :=
  congrArg (fun b => b i)
    ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U n W).apply_symm_apply _)

theorem cechMultiplySections_add (W : X.Opens) (a b : Γ(TermModules.cechTermModule X U n, W)) :
    cechMultiplySections U n r W (a + b) = cechMultiplySections U n r W a + cechMultiplySections U n r W b := by
  apply (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U n W).injective
  funext i
  change cechCoefficient U n W _ i = cechCoefficient U n W _ i
  rw [cechMultiplySections_coefficient, cechCoefficient_add, cechCoefficient_add,
    cechMultiplySections_coefficient, cechMultiplySections_coefficient, mul_add]

theorem cechMultiplySections_smul (W : X.Opens) (s : Γ(X, W)) (a : Γ(TermModules.cechTermModule X U n, W)) :
    cechMultiplySections U n r W (s • a) = s • cechMultiplySections U n r W a := by
  apply (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U n W).injective
  funext i
  change cechCoefficient U n W _ i = cechCoefficient U n W _ i
  rw [cechMultiplySections_coefficient, cechCoefficient_smul, cechCoefficient_smul,
    cechMultiplySections_coefficient, mul_left_comm]

theorem cechMultiplySections_restrict {V W : X.Opens} (h : W ≤ V)
    (a : Γ(TermModules.cechTermModule X U n, V)) :
    cechMultiplySections U n r W ((TermModules.cechTermModule X U n).presheaf.map (homOfLE h).op a) =
      (TermModules.cechTermModule X U n).presheaf.map (homOfLE h).op (cechMultiplySections U n r V a) := by
  apply (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U n W).injective
  funext i
  change cechCoefficient U n W _ i = cechCoefficient U n W _ i
  rw [cechMultiplySections_coefficient, cechCoefficient_restrict, cechCoefficient_restrict,
    cechMultiplySections_coefficient, map_mul]
  congr 1
  exact (ConcreteCategory.congr_hom ((X.presheaf.map_comp _ _).symm.trans
    (congrArg X.presheaf.map (Subsingleton.elim _ _))) (r i)).symm

local instance cechCoefficientRingModule (W : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj W) ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (TermModules.structureAbelianSheaf X) U n).obj.obj W) :=
  TermModules.cechTermSectionModule X U n W.unop

def cechCoefficientMultiplication : End (TermModules.cechTermModule X U n) where
  val := {
    app W := ModuleCat.ofHom {
      toFun := cechMultiplySections U n r W.unop
      map_add' := cechMultiplySections_add U n r W.unop
      map_smul' := cechMultiplySections_smul U n r W.unop }
    naturality := by
      intro V W f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact cechMultiplySections_restrict U n r (leOfHom f.unop) a }

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates
