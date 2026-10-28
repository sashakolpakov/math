import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechGenerator
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.PairCoordinates

/-! # Local -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Local

noncomputable section

section

/-! Degree-zero Cech coordinates restrict to their literal regular
functions on any open contained in the chosen frame domain. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)

theorem cechZeroIndex_eq (a : Fin 1 → I) : a = PairCoordinates.cechSingletonIndex (a 0) := by
  funext k
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  rfl

def cechZeroValueOn (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W)) (j : I)
    (V : X.Opens) (hVW : V ≤ W) (hVj : V ≤ U j) : Γ(X, V) :=
  X.presheaf.map (homOfLE (le_inf hVW (hVj.trans (PairCoordinates.cechIntersection_singleton U j).ge))).op
    (ExtensionCoordinates.cechCoefficient U 0 W a (PairCoordinates.cechSingletonIndex j))

theorem cechZeroRestrictedCoefficient_congr (W : X.Opens) (s : Γ(TermModules.cechTermModule X U 0, W))
    {a b : Fin 1 → I} (hab : a = b) (V : X.Opens)
    (ha : V ≤ W ⊓ ExtensionCoordinates.cechIntersection U 0 a) (hb : V ≤ W ⊓ ExtensionCoordinates.cechIntersection U 0 b) :
    X.presheaf.map (homOfLE ha).op (ExtensionCoordinates.cechCoefficient U 0 W s a) =
      X.presheaf.map (homOfLE hb).op (ExtensionCoordinates.cechCoefficient U 0 W s b) := by
  cases hab
  rfl

theorem cechZeroValueOn_restrict (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W)) (j : I)
    {V Z : X.Opens} (hZV : Z ≤ V) (hVW : V ≤ W) (hVj : V ≤ U j) :
    X.presheaf.map (homOfLE hZV).op (cechZeroValueOn U W a j V hVW hVj) =
      cechZeroValueOn U W a j Z (hZV.trans hVW) (hZV.trans hVj) :=
  ConcreteCategory.congr_hom (X.presheaf.map_comp _ _).symm _

theorem cechZeroValueOn_same (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W)) (j : I) :
    cechZeroValueOn U W a j (W ⊓ ExtensionCoordinates.cechIntersection U 0 (PairCoordinates.cechSingletonIndex j)) inf_le_left
      (inf_le_right.trans (PairCoordinates.cechIntersection_singleton U j).le) =
        ExtensionCoordinates.cechCoefficient U 0 W a (PairCoordinates.cechSingletonIndex j) := by
  change X.presheaf.map (𝟙 (.op (W ⊓ ExtensionCoordinates.cechIntersection U 0 (PairCoordinates.cechSingletonIndex j)))) _ = _
  exact ConcreteCategory.congr_hom (X.presheaf.map_id _) _

theorem cechZeroValueOn_coefficient (W : X.Opens) (s : Γ(TermModules.cechTermModule X U 0, W)) (a : Fin 1 → I) :
    cechZeroValueOn U W s (a 0) (W ⊓ ExtensionCoordinates.cechIntersection U 0 a) inf_le_left
      (inf_le_right.trans (Regular.CechGenerator.cechIntersection_le_component U 0 a 0)) = ExtensionCoordinates.cechCoefficient U 0 W s a := by
  have h := cechZeroRestrictedCoefficient_congr U W s (cechZeroIndex_eq a)
    (W ⊓ ExtensionCoordinates.cechIntersection U 0 a) le_rfl
    (le_inf inf_le_left ((inf_le_right.trans (Regular.CechGenerator.cechIntersection_le_component U 0 a 0)).trans
      (PairCoordinates.cechIntersection_singleton U (a 0)).ge))
  exact h.symm.trans (ConcreteCategory.congr_hom (X.presheaf.map_id _) _)

theorem cechZeroValueOn_smul (W : X.Opens) (s : Γ(X, W)) (a : Γ(TermModules.cechTermModule X U 0, W))
    (j : I) (V : X.Opens) (hVW : V ≤ W) (hVj : V ≤ U j) :
    cechZeroValueOn U W (s • a) j V hVW hVj =
      X.presheaf.map (homOfLE hVW).op s * cechZeroValueOn U W a j V hVW hVj := by
  unfold cechZeroValueOn
  rw [ExtensionCoordinates.cechCoefficient_smul, map_mul]
  congr 1
  exact ConcreteCategory.congr_hom (X.presheaf.map_comp _ _).symm s

theorem cechZeroValueOn_generator (r : Regular.TransitionCocycle.RegularTransitionCoefficients U) (j : I)
    (W : X.Opens) (hW : W ≤ U j) (i : I) (V : X.Opens) (hVW : V ≤ W) (hVi : V ≤ U i) :
    cechZeroValueOn U W (Regular.CechGenerator.regularCechGenerator U r j W hW) i V hVW hVi =
      (Regular.TransitionCocycle.regularTransitionOn U r j i V (hVW.trans hW) hVi).val := by
  unfold cechZeroValueOn
  rw [Regular.CechGenerator.regularCechGenerator_coefficient, Regular.CechGenerator.regularTransitionOn_restrict_val]
  rfl

theorem cechZeroValueOn_generator_self (r : Regular.TransitionCocycle.RegularTransitionCoefficients U)
    (hr : Regular.TransitionCocycle.RegularTransitionCocycle U r) (j : I) (W : X.Opens) (hW : W ≤ U j) :
    cechZeroValueOn U W (Regular.CechGenerator.regularCechGenerator U r j W hW) j W le_rfl hW = 1 := by
  rw [cechZeroValueOn_generator]
  exact congrArg Units.val (Regular.TransitionCocycle.regularTransition_self_on U r hr j W hW)

end

section

/-! Compatible original Cech coordinates satisfy the literal
pairwise transition equation on every smaller algebraic overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens) (r : Regular.TransitionCocycle.RegularTransitionCoefficients U)

theorem cechCompatible_pair_values (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W))
    (ha : LineSections.CechLineCompatible U (Regular.CechGenerator.regularCechCoefficients U r) W a)
    (i j : I) (V : X.Opens) (hVW : V ≤ W) (hVi : V ≤ U i) (hVj : V ≤ U j) :
    cechZeroValueOn U W a j V hVW hVj =
      (Regular.TransitionCocycle.regularTransitionOn U r i j V hVi hVj).val * cechZeroValueOn U W a i V hVW hVi := by
  let b := PairCoordinates.cechPairIndex i j
  have hV : V ≤ W ⊓ ExtensionCoordinates.cechIntersection U 1 b :=
    le_inf hVW ((le_inf hVi hVj).trans (PairCoordinates.cechIntersection_pair U i j).ge)
  have h := congrArg (X.presheaf.map (homOfLE hV).op) (ha b)
  have hface (k : Fin 2) :
      X.presheaf.map (homOfLE hV).op
        (X.presheaf.map (homOfLE (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 k b))).op
          (ExtensionCoordinates.cechCoefficient U 0 W a (ExtensionCoordinates.cechFaceIndex 0 k b))) =
      X.presheaf.map (homOfLE (hV.trans (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 k b)))).op
        (ExtensionCoordinates.cechCoefficient U 0 W a (ExtensionCoordinates.cechFaceIndex 0 k b)) :=
    ConcreteCategory.congr_hom (X.presheaf.map_comp _ _).symm _
  have hr : X.presheaf.map (homOfLE hV).op
      (X.presheaf.map (homOfLE (show W ⊓ ExtensionCoordinates.cechIntersection U 1 b ≤ ExtensionCoordinates.cechIntersection U 1 b
        from inf_le_right)).op (Regular.CechGenerator.regularCechCoefficients U r b)) =
      (Regular.TransitionCocycle.regularTransitionOn U r i j V hVi hVj).val := by
    have hp := ConcreteCategory.congr_hom (X.presheaf.map_comp
      (homOfLE (show W ⊓ ExtensionCoordinates.cechIntersection U 1 b ≤ ExtensionCoordinates.cechIntersection U 1 b from inf_le_right)).op
      (homOfLE hV).op).symm (Regular.CechGenerator.regularCechCoefficients U r b)
    exact hp.trans (Regular.CechGenerator.regularCechCoefficients_restrict U r b (hV.trans inf_le_right))
  rw [map_mul, hface 0, hface 1, hr] at h
  have h0 : X.presheaf.map
      (homOfLE (hV.trans (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 0 b)))).op
        (ExtensionCoordinates.cechCoefficient U 0 W a (ExtensionCoordinates.cechFaceIndex 0 0 b)) = cechZeroValueOn U W a j V hVW hVj :=
    cechZeroRestrictedCoefficient_congr U W a (PairCoordinates.cechPairIndex_face_zero i j) V _ _
  have h1 : X.presheaf.map
      (homOfLE (hV.trans (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 1 b)))).op
        (ExtensionCoordinates.cechCoefficient U 0 W a (ExtensionCoordinates.cechFaceIndex 0 1 b)) = cechZeroValueOn U W a i V hVW hVi :=
    cechZeroRestrictedCoefficient_congr U W a (PairCoordinates.cechPairIndex_face_one i j) V _ _
  exact h0.symm.trans (h.trans (congrArg ((Regular.TransitionCocycle.regularTransitionOn U r i j V hVi hVj).val * ·) h1))

end

section

/-! Every compatible local coordinate tuple is uniquely determined
by its chosen coordinate and the constructed cocycle generator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.TopCat.Sheaf

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens) (r : Regular.TransitionCocycle.RegularTransitionCoefficients U)

theorem cechCompatible_eq_generator (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W))
    (ha : LineSections.CechLineCompatible U (Regular.CechGenerator.regularCechCoefficients U r) W a) (j : I) (hW : W ≤ U j) :
    a = cechZeroValueOn U W a j W le_rfl hW • Regular.CechGenerator.regularCechGenerator U r j W hW := by
  apply (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U 0 W).injective
  funext b
  change ExtensionCoordinates.cechCoefficient U 0 W _ b = ExtensionCoordinates.cechCoefficient U 0 W _ b
  rw [ExtensionCoordinates.cechCoefficient_smul, Regular.CechGenerator.regularCechGenerator_coefficient]
  have hb := cechZeroValueOn_coefficient U W a b
  have hp := cechCompatible_pair_values U r W a ha j (b 0) (W ⊓ ExtensionCoordinates.cechIntersection U 0 b)
    inf_le_left (inf_le_left.trans hW) (inf_le_right.trans (Regular.CechGenerator.cechIntersection_le_component U 0 b 0))
  have hj := cechZeroValueOn_restrict U W a j
    (show W ⊓ ExtensionCoordinates.cechIntersection U 0 b ≤ W from inf_le_left) le_rfl hW
  exact hb.symm.trans (hp.trans ((congrArg
    ((Regular.TransitionCocycle.regularTransitionOn U r j (b 0) (W ⊓ ExtensionCoordinates.cechIntersection U 0 b) (inf_le_left.trans hW)
      (inf_le_right.trans (Regular.CechGenerator.cechIntersection_le_component U 0 b 0))).val * ·) hj.symm).trans (mul_comm _ _)))

theorem cechGenerator_smul_coordinate (hr : Regular.TransitionCocycle.RegularTransitionCocycle U r)
    (j : I) (W : X.Opens) (hW : W ≤ U j) (s : Γ(X, W)) :
    cechZeroValueOn U W (s • Regular.CechGenerator.regularCechGenerator U r j W hW) j W le_rfl hW = s := by
  rw [cechZeroValueOn_smul, cechZeroValueOn_generator_self U r hr, mul_one]
  exact ConcreteCategory.congr_hom (X.presheaf.map_id _) s

theorem cechGenerator_smul_injective (hr : Regular.TransitionCocycle.RegularTransitionCocycle U r)
    (j : I) (W : X.Opens) (hW : W ≤ U j) :
    Function.Injective (fun s : Γ(X, W) => s • Regular.CechGenerator.regularCechGenerator U r j W hW) := by
  intro s t h
  have hv := congrArg (fun a => cechZeroValueOn U W a j W le_rfl hW) h
  rw [cechGenerator_smul_coordinate U r hr, cechGenerator_smul_coordinate U r hr] at hv
  exact hv

end

/-! The constructed cocycle generator is a basis of the sections
of the actual kernel sheaf on every smaller frame open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens) (r : Regular.TransitionCocycle.RegularTransitionCoefficients U)
    (hr : Regular.TransitionCocycle.RegularTransitionCocycle U r)

def regularCechLineLocalGenerator (j : I) (W : X.Opens) (hW : W ≤ U j) :
    Γ(LineModule.cechLineModule U (Regular.CechGenerator.regularCechCoefficients U r), W) :=
  (LineModule.cechLineModule U (Regular.CechGenerator.regularCechCoefficients U r)).presheaf.map (homOfLE hW).op
    (Regular.CechGenerator.regularCechLineGenerator U r hr j)

theorem regularCechLineLocalGenerator_inclusion (j : I) (W : X.Opens) (hW : W ≤ U j) :
    (LineModule.cechLineModuleInclusion U (Regular.CechGenerator.regularCechCoefficients U r)).app W
      (regularCechLineLocalGenerator U r hr j W hW) = Regular.CechGenerator.regularCechGenerator U r j W hW := by
  have h := ConcreteCategory.congr_hom
    ((LineModule.cechLineModuleInclusion U (Regular.CechGenerator.regularCechCoefficients U r)).mapPresheaf.naturality (homOfLE hW).op)
    (Regular.CechGenerator.regularCechLineGenerator U r hr j)
  exact h.trans ((congrArg ((TermModules.cechTermModule X U 0).presheaf.map (homOfLE hW).op)
    (Regular.CechGenerator.regularCechLineGenerator_inclusion U r hr j)).trans (Regular.CechGenerator.regularCechGenerator_restrict U r j hW le_rfl))

theorem regularCechLineLocalGenerator_smul_inclusion (j : I) (W : X.Opens) (hW : W ≤ U j) (s : Γ(X, W)) :
    (LineModule.cechLineModuleInclusion U (Regular.CechGenerator.regularCechCoefficients U r)).app W
      (s • regularCechLineLocalGenerator U r hr j W hW) = s • Regular.CechGenerator.regularCechGenerator U r j W hW := by
  have h := (ModuleKernelSections.moduleSectionLinearMap (LineModule.cechLineModuleInclusion U (Regular.CechGenerator.regularCechCoefficients U r)) W).map_smul
    s (regularCechLineLocalGenerator U r hr j W hW)
  exact h.trans (congrArg (s • ·) (regularCechLineLocalGenerator_inclusion U r hr j W hW))

theorem regularCechLineLocalGenerator_bijective (j : I) (W : X.Opens) (hW : W ≤ U j) :
    Function.Bijective (fun s : Γ(X, W) => s • regularCechLineLocalGenerator U r hr j W hW) := by
  constructor
  · intro s t h
    apply cechGenerator_smul_injective U r hr j W hW
    exact (regularCechLineLocalGenerator_smul_inclusion U r hr j W hW s).symm.trans
      ((congrArg ((LineModule.cechLineModuleInclusion U (Regular.CechGenerator.regularCechCoefficients U r)).app W) h).trans
        (regularCechLineLocalGenerator_smul_inclusion U r hr j W hW t))
  · intro m
    let a := (LineModule.cechLineModuleInclusion U (Regular.CechGenerator.regularCechCoefficients U r)).app W m
    have ha : LineSections.CechLineCompatible U (Regular.CechGenerator.regularCechCoefficients U r) W a :=
      fun i => LineModule.cechLineModule_section_relation U (Regular.CechGenerator.regularCechCoefficients U r) W m i
    let s := cechZeroValueOn U W a j W le_rfl hW
    refine ⟨s, ?_⟩
    apply LineSections.cechLineModule_sections_injective U (Regular.CechGenerator.regularCechCoefficients U r) W
    exact (regularCechLineLocalGenerator_smul_inclusion U r hr j W hW s).trans
      (cechCompatible_eq_generator U r W a ha j hW).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Local
