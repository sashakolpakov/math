import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App

/-! # Extension Of -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionOf.CohomologyExtension

noncomputable section

/-! Actual degree-one extensions and their torsors for arbitrary additive coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Abelian

open OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction

universe u
variable (X : Scheme.{u}) (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})

/-- Extension data with the actual coefficient sheaf and integer source. -/
structure Extension where
  middle : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  inclusion : F ⟶ middle
  projection : middle ⟶ AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X
  zero : inclusion ≫ projection = 0
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

namespace Extension

variable {X F} (E : Extension X F)

def complex : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  ShortComplex.mk E.inclusion E.projection E.zero

def extClass : (F).H 1 := E.shortExact.extClass

instance : Mono E.inclusion := E.shortExact.mono_f
instance : Epi E.projection := E.shortExact.epi_g

end Extension

/-- Every actual coefficient H¹ class has such an extension representative. -/
theorem extension_exists (x : (F).H 1) :
    ∃ E : Extension X F, E.extClass = x := by
  obtain ⟨M, i, p, h, hS, hx⟩ := AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions.Construction.ext_one_exists_shortExact x
  exact ⟨⟨M, i, p, h, hS⟩, hx⟩

/-- A chosen representative, obtained from the checked Ext¹ presentation. -/
def extensionOfClass (x : (F).H 1) :
    Extension X F := (extension_exists X F x).choose

theorem extensionOfClass_class (x : (F).H 1) :
    (extensionOfClass X F x).extClass = x :=
  (extension_exists X F x).choose_spec

namespace Extension

variable {X F} (E : Extension X F)

/-- Sections of the fiber over the integer generator. -/
def Fiber (U : X.ProEt) :=
  {s : E.middle.obj.obj (op U) // E.projection.hom.app (op U) s =
    AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U}

/-- Restriction in the torsor of lifts of the generator. -/
def restrict {U V : X.ProEt} (f : V ⟶ U) (s : E.Fiber U) : E.Fiber V :=
  ⟨E.middle.obj.map f.op s.val, by
    erw [NatTrans.naturality_apply, s.property, AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator_naturality]⟩

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
    Presheaf.imageSieve E.projection.hom (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U) ∈
      Scheme.ProEt.topology X U := by
  have : Sheaf.IsLocallySurjective E.projection :=
    (Sheaf.isLocallySurjective_iff_epi' Ab E.projection).mpr inferInstance
  exact Presheaf.imageSieve_mem _ _ _

/-- Every arrow in the covering sieve carries a local torsor section. -/
theorem fiber_nonempty_of_imageSieve {U V : X.ProEt} (f : V ⟶ U)
    (hf : Presheaf.imageSieve E.projection.hom (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U) f) :
    Nonempty (E.Fiber V) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, hs.trans (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator_naturality X f)⟩

/-- The inclusion and projection remain exact at the middle on sections. -/
theorem sections_exact (U : X.ProEt) :
    (E.complex.map ((sheafToPresheaf _ Ab.{u + 1}) ⋙ (evaluation _ _).obj (op U))).Exact :=
  ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mp inferInstance
    E.complex E.shortExact).1

theorem inclusion_app_injective (U : X.ProEt) :
    Function.Injective (E.inclusion.hom.app (op U)) := by
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- Two local torsor sections differ by a unique coefficient section. -/
theorem fiber_unique_difference (U : X.ProEt) (s t : E.Fiber U) :
    ∃! a : (F).obj.obj (op U),
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
  rw [Extension.extClass, AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions.Construction.extClass_eq_zero_iff_exists_section E.shortExact]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨Sheaf.H.equiv₀ E.middle terminalIsTerminal (Ext.mk₀ s), ?_⟩
    rw [Sheaf.H.equiv₀_naturality, AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator_terminal]
    change Sheaf.H.equiv₀ _ terminalIsTerminal
      ((Ext.mk₀ s).comp (Ext.mk₀ E.projection) (add_zero 0)) = _
    rw [Ext.mk₀_comp_mk₀, hs]
    rfl
  · rintro ⟨s⟩
    let y := (Sheaf.H.equiv₀ E.middle terminalIsTerminal).symm s.val
    obtain ⟨t, ht⟩ := (Ext.mk₀_bijective _ _).surjective y
    refine ⟨t, (Ext.mk₀_bijective _ _).injective ?_⟩
    apply (Sheaf.H.equiv₀ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) terminalIsTerminal).injective
    rw [← Ext.mk₀_comp_mk₀]
    change Sheaf.H.equiv₀ _ terminalIsTerminal (Sheaf.H.map E.projection 0 (Ext.mk₀ t)) = _
    rw [← Sheaf.H.equiv₀_naturality, ht]
    change E.projection.hom.app _ ((Sheaf.H.equiv₀ E.middle terminalIsTerminal)
      ((Sheaf.H.equiv₀ E.middle terminalIsTerminal).symm s.val)) = _
    rw [AddEquiv.apply_symm_apply, s.property, AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator_terminal]
    rfl

end Extension

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionOf.CohomologyExtension
