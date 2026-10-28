import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # App -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction

noncomputable section

/-!
# Completion: local torsors attached to actual finite-coefficient H¹ classes

An actual degree-one class is represented by an extension of the integer
constant sheaf. The inverse image of its canonical generator is locally
nonempty, and any two of its sections differ by a unique coefficient section.
A global section of this torsor is equivalent to vanishing of the class.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ n : ℕ) (X : Scheme.{u})

/-- Extension data with the actual finite coefficient sheaf and integer source. -/
structure FiniteCoefficientExtension where
  middle : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  inclusion : Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X ⟶ middle
  projection : middle ⟶ ProetalePullback.Construction.proEtIntegerConstant X
  zero : inclusion ≫ projection = 0
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

namespace FiniteCoefficientExtension

variable {ℓ n X} (E : FiniteCoefficientExtension ℓ n X)

def complex : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  ShortComplex.mk E.inclusion E.projection E.zero

def extClass : (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1 := E.shortExact.extClass

instance : Mono E.inclusion := E.shortExact.mono_f
instance : Epi E.projection := E.shortExact.epi_g

end FiniteCoefficientExtension

/-- Every actual finite-coefficient H¹ class has such an extension representative. -/
theorem finiteCoefficientExtension_exists (x : (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1) :
    ∃ E : FiniteCoefficientExtension ℓ n X, E.extClass = x := by
  obtain ⟨M, i, p, h, hS, hx⟩ := ExtExtensions.Construction.ext_one_exists_shortExact x
  exact ⟨⟨M, i, p, h, hS⟩, hx⟩

/-- A chosen representative, obtained from the checked Ext¹ presentation. -/
def finiteCoefficientExtensionOfClass (x : (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1) :
    FiniteCoefficientExtension ℓ n X := (finiteCoefficientExtension_exists ℓ n X x).choose

theorem finiteCoefficientExtensionOfClass_class (x : (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1) :
    (finiteCoefficientExtensionOfClass ℓ n X x).extClass = x :=
  (finiteCoefficientExtension_exists ℓ n X x).choose_spec

variable {ℓ n}

/-- The canonical generator of the integer constant sheaf at the terminal object. -/
def proEtIntegerGenerator : (ProetalePullback.Construction.proEtIntegerConstant X).obj.obj (op (⊤_ X.ProEt)) :=
  Sheaf.H.equiv₀ (ProetalePullback.Construction.proEtIntegerConstant X) terminalIsTerminal (Ext.mk₀ (𝟙 _))

/-- The same generator restricted to any object of the actual site. -/
def proEtIntegerLocalGenerator (U : X.ProEt) : (ProetalePullback.Construction.proEtIntegerConstant X).obj.obj (op U) :=
  (ProetalePullback.Construction.proEtIntegerConstant X).obj.map (terminal.from U).op (proEtIntegerGenerator X)

@[simp]
theorem proEtIntegerLocalGenerator_terminal :
    proEtIntegerLocalGenerator X (⊤_ X.ProEt) = proEtIntegerGenerator X := by
  have h : terminal.from (⊤_ X.ProEt) = 𝟙 _ := terminalIsTerminal.hom_ext _ _
  simp [proEtIntegerLocalGenerator, h]

theorem proEtIntegerLocalGenerator_naturality {U V : X.ProEt} (f : V ⟶ U) :
    (ProetalePullback.Construction.proEtIntegerConstant X).obj.map f.op (proEtIntegerLocalGenerator X U) =
      proEtIntegerLocalGenerator X V := by
  simp only [proEtIntegerLocalGenerator, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, terminal.comp_from]

namespace FiniteCoefficientExtension

variable {X} (E : FiniteCoefficientExtension ℓ n X)

/-- Sections of the fiber over the integer generator. -/
def Fiber (U : X.ProEt) :=
  {s : E.middle.obj.obj (op U) // E.projection.hom.app (op U) s =
    proEtIntegerLocalGenerator X U}

/-- Restriction in the torsor of lifts of the generator. -/
def restrict {U V : X.ProEt} (f : V ⟶ U) (s : E.Fiber U) : E.Fiber V :=
  ⟨E.middle.obj.map f.op s.val, by
    erw [NatTrans.naturality_apply, s.property, proEtIntegerLocalGenerator_naturality]⟩

/-- The presheaf of local lifts of the integer generator. -/
def fiberPresheaf : X.ProEtᵒᵖ ⥤ Type (u + 1) where
  obj U := E.Fiber U.unop
  map f := ↾(E.restrict f.unop)
  map_id U := by ext s; apply Subtype.ext; exact ConcreteCategory.congr_hom (E.middle.obj.map_id U) _
  map_comp f g := by
    ext s
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (E.middle.obj.map_comp f g) _

/-- The torsor is locally inhabited in the actual pro-étale topology. -/
theorem fiber_locally_nonempty (U : X.ProEt) :
    Presheaf.imageSieve E.projection.hom (proEtIntegerLocalGenerator X U) ∈
      Scheme.ProEt.topology X U := by
  have : Sheaf.IsLocallySurjective E.projection :=
    (Sheaf.isLocallySurjective_iff_epi' Ab E.projection).mpr inferInstance
  exact Presheaf.imageSieve_mem _ _ _

/-- Every arrow in the covering sieve carries a local torsor section. -/
theorem fiber_nonempty_of_imageSieve {U V : X.ProEt} (f : V ⟶ U)
    (hf : Presheaf.imageSieve E.projection.hom (proEtIntegerLocalGenerator X U) f) :
    Nonempty (E.Fiber V) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, hs.trans (proEtIntegerLocalGenerator_naturality X f)⟩

/-- The inclusion and projection remain exact at the middle on sections. -/
theorem sections_exact (U : X.ProEt) :
    (E.complex.map ((sheafToPresheaf _ Ab.{u + 1}) ⋙ (evaluation _ _).obj (op U))).Exact :=
  ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mp inferInstance
    E.complex E.shortExact).1

theorem inclusion_app_injective (U : X.ProEt) :
    Function.Injective (E.inclusion.hom.app (op U)) := by
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- Two local torsor sections differ by a unique actual coefficient section. -/
theorem fiber_unique_difference (U : X.ProEt) (s t : E.Fiber U) :
    ∃! a : (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.obj (op U),
      E.inclusion.hom.app (op U) a + s.val = t.val := by
  have h : E.projection.hom.app (op U) (t.val - s.val) = 0 := by
    rw [map_sub, t.property, s.property, sub_self]
  obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff _).mp (E.sections_exact U) _ h
  refine ⟨a, (eq_sub_iff_add_eq).mp ha, ?_⟩
  intro b hb
  apply E.inclusion_app_injective U
  exact (eq_sub_iff_add_eq.mpr hb).trans ha.symm

/-- A global torsor section is equivalent to a split extension. -/
theorem class_eq_zero_iff_fiber_nonempty : E.extClass = 0 ↔ Nonempty (E.Fiber (⊤_ X.ProEt)) := by
  rw [FiniteCoefficientExtension.extClass, ExtExtensions.Construction.extClass_eq_zero_iff_exists_section E.shortExact]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨Sheaf.H.equiv₀ E.middle terminalIsTerminal (Ext.mk₀ s), ?_⟩
    rw [Sheaf.H.equiv₀_naturality, proEtIntegerLocalGenerator_terminal]
    change Sheaf.H.equiv₀ _ terminalIsTerminal
      ((Ext.mk₀ s).comp (Ext.mk₀ E.projection) (add_zero 0)) = _
    rw [Ext.mk₀_comp_mk₀, hs]
    rfl
  · rintro ⟨s⟩
    let y := (Sheaf.H.equiv₀ E.middle terminalIsTerminal).symm s.val
    obtain ⟨t, ht⟩ := (Ext.mk₀_bijective _ _).surjective y
    refine ⟨t, (Ext.mk₀_bijective _ _).injective ?_⟩
    apply (Sheaf.H.equiv₀ (ProetalePullback.Construction.proEtIntegerConstant X) terminalIsTerminal).injective
    rw [← Ext.mk₀_comp_mk₀]
    change Sheaf.H.equiv₀ _ terminalIsTerminal (Sheaf.H.map E.projection 0 (Ext.mk₀ t)) = _
    rw [← Sheaf.H.equiv₀_naturality, ht]
    change E.projection.hom.app _ ((Sheaf.H.equiv₀ E.middle terminalIsTerminal)
      ((Sheaf.H.equiv₀ E.middle terminalIsTerminal).symm s.val)) = _
    rw [AddEquiv.apply_symm_apply, s.property, proEtIntegerLocalGenerator_terminal]
    rfl

end FiniteCoefficientExtension

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction
