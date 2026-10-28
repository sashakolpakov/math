import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Flasque Low Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueLowDegree

noncomputable section

/-!
# Low-degree cohomology of a flasque sheaf complex

For a complex of sheaves of abelian groups indexed by natural numbers, exactness
below a degree propagates flasqueness to its successive cokernels. This makes
the comparison with the cohomology of global sections an actual isomorphism in
that degree. The section functor is never assumed to be exact on all sheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

universe u

/-- Evaluation of a genuine sheaf of abelian groups on the top open subset. -/
def sheafGlobalSections (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

instance sheafGlobalSections_additive (X : TopCat.{u}) :
    (sheafGlobalSections X).Additive where
  map_add := rfl

instance sheafGlobalSections_preservesFiniteLimits (X : TopCat.{u}) :
    PreservesFiniteLimits (sheafGlobalSections X) := by
  have : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X) := inferInstance
  have : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) := inferInstance
  exact comp_preservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))

/-- The ordinary cochain complex obtained by taking global sections degreewise. -/
def sheafGlobalSectionsComplex {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  ((sheafGlobalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- Flasqueness is invariant under an actual isomorphism of sheaves. -/
theorem flasqueSheaf_of_iso {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ≅ G)
    [TopCat.Sheaf.IsFlasque F] : TopCat.Sheaf.IsFlasque G := by
  let e' := (TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapIso e
  constructor
  intro U V i
  have he : Epi (e'.hom.app U ≫ G.obj.map i) := by
    change Epi (e'.hom.app U ≫ ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).obj G).map i)
    rw [← e'.hom.naturality]
    have : Epi (((TopCat.Sheaf.forget AddCommGrpCat.{u} X).obj F).map i) := by
      change Epi (F.obj.map i)
      infer_instance
    infer_instance
  exact epi_of_epi (e'.hom.app U) (G.obj.map i)

/-- A zero sheaf is flasque, since all of its groups of sections are zero. -/
theorem flasqueSheaf_of_isZero {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : IsZero F) :
    TopCat.Sheaf.IsFlasque F := by
  constructor
  intro U V i
  have hzero := ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj V).map_isZero
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map_isZero hF)
  exact hzero.epi (F.obj.map i)

/-- Global sections preserve a short exact sheaf sequence whose first term is
flasque. The epimorphism conclusion uses the sheaf gluing theorem. -/
theorem flasqueSheafSequence_global_shortExact {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] :
    (S.map (sheafGlobalSections X)).ShortExact := by
  have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (sheafGlobalSections X)).1 inferInstance S hS
  have hep : Epi ((sheafGlobalSections X).map S.g) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
  exact ShortComplex.ShortExact.mk' hleft.1 hleft.2 hep

section SuccessiveCokernels

variable {C : Type*} [Category* C] [Abelian C]
  (K : CochainComplex C ℕ) (n : ℕ)

/-- The successor sequence is built from the actual cokernels of the incoming
differentials, not from a chosen quotient model. -/
abbrev opcyclesSuccessorSequence : ShortComplex C :=
  ShortComplex.mk (K.fromOpcycles n (n + 1)) (K.pOpcycles (n + 1)) (by
    rw [← cancel_epi (K.pOpcycles n), comp_zero,
      HomologicalComplex.p_fromOpcycles_assoc, HomologicalComplex.d_pOpcycles])

/-- The successor sequence is always right exact. -/
theorem opcyclesSuccessorSequence_exact : (opcyclesSuccessorSequence K n).Exact := by
  let S := ShortComplex.mk (K.d n (n + 1)) (K.pOpcycles (n + 1))
    (K.d_pOpcycles n (n + 1))
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (K.opcyclesIsCokernel n (n + 1) (by simp))
  let φ : S ⟶ opcyclesSuccessorSequence K n :=
    { τ₁ := K.pOpcycles n
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, opcyclesSuccessorSequence]
      comm₂₃ := by simp [S, opcyclesSuccessorSequence] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS

/-- Vanishing cohomology in degree `n` makes the successor sequence short exact. -/
theorem opcyclesSuccessorSequence_shortExact (h : K.ExactAt n) :
    (opcyclesSuccessorSequence K n).ShortExact := by
  have hm : Mono (K.fromOpcycles n (n + 1)) :=
    mono_of_isZero_kernel' _ (K.homologyIsKernel n (n + 1) (by simp))
      h.isZero_homology
  exact ShortComplex.ShortExact.mk' (opcyclesSuccessorSequence_exact K n)
    hm inferInstance

/-- The kernel of the canonical opcycle projection is precisely the actual
abelian image of the incoming differential. -/
def opcyclesKernelIsoImage : kernel (K.pOpcycles n) ≅ Abelian.image (K.sc n).f :=
  kernel.mapIso (K.pOpcycles n) (cokernel.π (K.sc n).f) (Iso.refl _)
    (K.sc n).opcyclesIsoCokernel (by
      change (K.sc n).pOpcycles ≫ (K.sc n).opcyclesIsoCokernel.hom =
        𝟙 _ ≫ cokernel.π (K.sc n).f
      simp)

/-- The first boundary object is zero because the complex starts in degree zero. -/
theorem cochainBoundary_zero_isZero : IsZero (Abelian.image (K.sc 0).f) :=
  (isZero_kernel_of_mono (K.pOpcycles 0)).of_iso (opcyclesKernelIsoImage K 0).symm

/-- Under exactness, the preceding opcycle object is the actual next boundary
object. This isomorphism is induced by the differential. -/
def opcyclesIsoSuccessorBoundary (h : K.ExactAt n) :
    K.opcycles n ≅ Abelian.image (K.sc (n + 1)).f := by
  have hS := opcyclesSuccessorSequence_shortExact K n h
  letI := hS.mono_f
  exact (IsLimit.conePointUniqueUpToIso hS.exact.fIsKernel
    (kernelIsKernel (K.pOpcycles (n + 1)))) ≪≫ opcyclesKernelIsoImage K (n + 1)

end SuccessiveCokernels

/-- Exactness in all earlier degrees makes the actual incoming-differential
cokernel flasque, starting with `opcycles 0 ≅ K⁰`. -/
theorem flasque_opcycles_of_exact_below {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) :
    ∀ n, n ≤ d → TopCat.Sheaf.IsFlasque (K.opcycles n) := by
  intro n
  induction n with
  | zero =>
      intro _
      have := hK 0
      exact flasqueSheaf_of_iso K.opcycles₀Iso
  | succ n ih =>
      intro hn
      have := ih (Nat.le_of_succ_le hn)
      have := hK (n + 1)
      exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))

/-- All boundary sheaves through degree `d` are flasque. These are actual
abelian images of the incoming differentials, with zero image in degree zero. -/
theorem flasque_boundaries_of_exact_below {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n ≤ d) :
    TopCat.Sheaf.IsFlasque (Abelian.image (K.sc n).f) := by
  cases n with
  | zero => exact flasqueSheaf_of_isZero _ (cochainBoundary_zero_isZero K)
  | succ n =>
      have := flasque_opcycles_of_exact_below K hK d he n (Nat.le_of_succ_le hn)
      exact flasqueSheaf_of_iso
        (opcyclesIsoSuccessorBoundary K n (he n (Nat.lt_of_succ_le hn)))

/-- Global sections surject onto the actual cokernel in every degree through
the first potentially nonzero cohomology degree. -/
theorem epi_globalSections_pOpcycles_of_exact_below {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n ≤ d) :
    Epi ((sheafGlobalSections X).map (K.pOpcycles n)) := by
  cases n with
  | zero => infer_instance
  | succ n =>
      have := flasque_opcycles_of_exact_below K hK d he n (Nat.le_of_succ_le hn)
      exact (flasqueSheafSequence_global_shortExact (X := X)
        (opcyclesSuccessorSequence K n)
        (opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))).epi_g

/-- The individual incoming cokernel is preserved by global sections in the
range where the earlier cohomology sheaves vanish. -/
theorem globalSections_preserves_incoming_cokernel {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n ≤ d) :
    PreservesColimit (parallelPair (K.sc n).f 0) (sheafGlobalSections X) := by
  cases n with
  | zero =>
      apply preservesCokernel_zero'
      change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
      simp
  | succ n =>
      change PreservesColimit
        (parallelPair (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)) 0)
        (sheafGlobalSections X)
      rw [CochainComplex.prev_nat_succ]
      have := flasque_opcycles_of_exact_below K hK d he n (Nat.le_of_succ_le hn)
      have := epi_globalSections_pOpcycles_of_exact_below K hK d he n
        (Nat.le_of_succ_le hn)
      let S := opcyclesSuccessorSequence K n
      have hS := flasqueSheafSequence_global_shortExact (X := X) S
        (opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))
      have := hS.epi_g
      refine preservesColimit_of_preserves_colimit_cocone
        (K.opcyclesIsCokernel n (n + 1) (by simp)) ?_
      apply (CokernelCofork.isColimitMapCoconeEquiv _ (sheafGlobalSections X)).2
      exact isCokernelEpiComp hS.exact.gIsCokernel
        ((sheafGlobalSections X).map (K.pOpcycles n)) (by
          change (sheafGlobalSections X).map (K.d n (n + 1)) =
            (sheafGlobalSections X).map (K.pOpcycles n) ≫
              (sheafGlobalSections X).map (K.fromOpcycles n (n + 1))
          rw [← Functor.map_comp, HomologicalComplex.p_fromOpcycles])

/-- Local preservation of right homology follows from the proved cokernel
preservation and the left exactness of global sections. -/
theorem globalSections_preservesRightHomologyOf {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n ≤ d) :
    (sheafGlobalSections X).PreservesRightHomologyOf (K.sc n) := by
  have := globalSections_preserves_incoming_cokernel K hK d he n hn
  constructor
  intro h
  exact { f := inferInstance, g' := inferInstance }

/-- The canonical cohomology comparison through the first potentially nonzero
degree of a flasque sheaf complex that starts in degree zero. -/
def flasqueLowDegreeHomologyIso {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n ≤ d) :
    (sheafGlobalSectionsComplex K).homology n ≅
      (sheafGlobalSections X).obj (K.homology n) := by
  letI := globalSections_preservesRightHomologyOf K hK d he n hn
  exact (K.sc n).mapHomologyIso' (sheafGlobalSections X)

/-- Global sections are exact below the first potentially nonzero sheaf
cohomology degree. -/
theorem flasqueLowDegree_exactAt {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n < d) :
    (sheafGlobalSectionsComplex K).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((sheafGlobalSections X).map_isZero (he n hn).isZero_homology).of_iso
    (flasqueLowDegreeHomologyIso K hK d he n hn.le)

/-- At the first degree, global cohomology is the group of global sections of
the genuine cohomology sheaf. -/
def flasqueFirstCohomologyIso {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) :
    (sheafGlobalSectionsComplex K).homology d ≅
      (sheafGlobalSections X).obj (K.homology d) :=
  flasqueLowDegreeHomologyIso K hK d he d le_rfl

/-- The comparison is canonical: it commutes with every morphism of the
underlying sheaf complexes, whenever both complexes satisfy the hypotheses. -/
theorem flasqueLowDegreeHomologyIso_naturality {X : TopCat.{u}}
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ}
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n))
    (d : ℕ) (heK : ∀ n, n < d → K.ExactAt n) (heL : ∀ n, n < d → L.ExactAt n)
    (n : ℕ) (hn : n ≤ d) (φ : K ⟶ L) :
    HomologicalComplex.homologyMap
        (((sheafGlobalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
      (flasqueLowDegreeHomologyIso L hL d heL n hn).hom =
        (flasqueLowDegreeHomologyIso K hK d heK n hn).hom ≫
          (sheafGlobalSections X).map (HomologicalComplex.homologyMap φ n) := by
  have := globalSections_preservesRightHomologyOf K hK d heK n hn
  have := globalSections_preservesRightHomologyOf L hL d heL n hn
  exact ShortComplex.mapHomologyIso'_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (sheafGlobalSections X)

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueLowDegree
