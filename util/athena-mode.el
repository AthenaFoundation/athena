;;; athena-mode.el --- Athena mode, slightly modified from Scheme (and DSSSL) editing mode.
;;; by DRM

;; Copyright (C) 1986, 87, 88, 97, 1998 Free Software Foundation, Inc.

;; Author: Bill Rozas <jinx@martigny.ai.mit.edu>
;; Adapted-by: Dave Love <d.love@dl.ac.uk>
;; Keywords: languages, lisp

;; This file is part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; The major mode for editing Athena-type Lisp code, very similar to
;; the Lisp mode documented in the Emacs manual.  `dsssl-mode' is a
;; variant of athena-mode for editing DSSSL specifications for SGML
;; documents.  [As of Apr 1997, some pointers for DSSSL may be found,
;; for instance, at <URL:http://www.sil.org/sgml/related.html#dsssl>.]
;; All these Lisp-ish modes vary basically in details of the language
;; syntax they highlight/indent/index, but dsssl-mode uses "^;;;" as
;; the page-delimiter since ^L isn't normally a legal SGML character.
;;
;; For interacting with a Scheme interpreter See also `run-scheme' in
;; the `cmuscheme' package and also the implementation-specific
;; `xscheme' package.

;; Here's a recipe to generate a TAGS file for DSSSL, by the way:
;; etags --lang=scheme --regex='/[ \t]*(\(mode\|element\)[ \t
;; ]+\([^ \t(
;; ]+\)/\2/' --regex='/[ \t]*(element[ \t
;; ]*([^)]+[ \t
;; ]+\([^)]+\)[ \t
;; ]*)/\1/' --regex='/(declare[^ \t
;; ]*[ \t
;; ]+\([^ \t
;; ]+\)/\1/' "$@"

;;; Code:

(require 'lisp-mode)

(defvar athena-mode-syntax-table nil "")
(if (not athena-mode-syntax-table)
    (let ((i 0))
      (setq athena-mode-syntax-table (make-syntax-table))
      (set-syntax-table athena-mode-syntax-table)

      ;; Default is atom-constituent.
      (while (< i 256)
	(modify-syntax-entry i "_   ")
	(setq i (1+ i)))

      ;; Word components.
      (setq i ?0)
      (while (<= i ?9)
	(modify-syntax-entry i "w   ")
	(setq i (1+ i)))
      (setq i ?A)
      (while (<= i ?Z)
	(modify-syntax-entry i "w   ")
	(setq i (1+ i)))
      (setq i ?a)
      (while (<= i ?z)
	(modify-syntax-entry i "w   ")
	(setq i (1+ i)))

      ;; Whitespace
      (modify-syntax-entry ?\t "    ")
      (modify-syntax-entry ?\n ">   ")
      (modify-syntax-entry ?\f "    ")
      (modify-syntax-entry ?\r "    ")
      (modify-syntax-entry ?  "    ")

      ;; These characters are delimiters but otherwise undefined.
      ;; Brackets and braces balance for editing convenience.
      (modify-syntax-entry ?\[ "(]  ")
      (modify-syntax-entry ?\] ")[  ")
      (modify-syntax-entry ?{ "(}  ")
      (modify-syntax-entry ?} "){  ")
      (modify-syntax-entry ?\| "  23")

      ;; Other atom delimiters
      (modify-syntax-entry ?\( "()  ")
      (modify-syntax-entry ?\) ")(  ")
      (modify-syntax-entry ?\# "<   ")
      (modify-syntax-entry ?\" "\"    ")
      (modify-syntax-entry ?' "  p")
      (modify-syntax-entry ?` "  p")

      ;; Special characters
      (modify-syntax-entry ?, "_ p")
      (modify-syntax-entry ?@ "_ p")
;      (modify-syntax-entry ?# "_ p14")
      (modify-syntax-entry ?\\ "\\   ")))

(defvar athena-mode-abbrev-table nil "")
(define-abbrev-table 'athena-mode-abbrev-table ())

(defvar athena-imenu-generic-expression
      '((nil 
	 "^(define\\(\\|-\\(generic\\(\\|-procedure\\)\\|method\\)\\)*\\s-+(?\\(\\sw+\\)" 4)
	("Types" 
	 "^(define-class\\s-+(?\\(\\sw+\\)" 1)
	("Macros"
	 "^(\\(defmacro\\|define-macro\\|define-syntax\\)\\s-+(?\\(\\sw+\\)" 2))
  "Imenu generic expression for Athena mode.  See `imenu-generic-expression'.")

(defun athena-mode-variables ()
  (set-syntax-table athena-mode-syntax-table)
  (setq local-abbrev-table athena-mode-abbrev-table)
  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'paragraph-ignore-fill-prefix)
  (setq paragraph-ignore-fill-prefix t)
  (make-local-variable 'fill-paragraph-function)
  (setq fill-paragraph-function 'lisp-fill-paragraph)
  ;; Adaptive fill mode gets in the way of auto-fill,
  ;; and should make no difference for explicit fill
  ;; because lisp-fill-paragraph should do the job.
  (make-local-variable 'adaptive-fill-mode)
  (setq adaptive-fill-mode nil)
  (make-local-variable 'normal-auto-fill-function)
  (setq normal-auto-fill-function 'lisp-mode-auto-fill)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'lisp-indent-line)
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments t)
  (make-local-variable 'outline-regexp)
  (setq outline-regexp ";;; \\|(....")
  (make-local-variable 'comment-start)
  (setq comment-start "#")
  (make-local-variable 'comment-start-skip)
  ;; Look within the line for a # following an even number of backslashes
  ;; after either a non-backslash or the line beginning.
  (setq comment-start-skip "\\(\\(^\\|[^\\\\\n]\\)\\(\\\\\\\\\\)*\\)#+[ \t]*")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-indent-function)
  (setq comment-indent-function 'lisp-comment-indent)
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments t)
  (make-local-variable 'lisp-indent-function)
  (set lisp-indent-function 'athena-indent-function)
  (setq mode-line-process '("" athena-mode-line-process))
  (make-local-variable 'imenu-case-fold-search)
  (setq imenu-case-fold-search t)
  (make-local-variable 'imenu-generic-expression)
  (setq imenu-generic-expression athena-imenu-generic-expression)
  (make-local-variable 'imenu-syntax-alist)
  (setq imenu-syntax-alist '(("+-*/.<>=?!$%_&~^:" . "w")))
  (make-local-variable 'font-lock-defaults)  
  (setq font-lock-defaults
        '((athena-font-lock-keywords
           athena-font-lock-keywords-1 athena-font-lock-keywords-2)
          nil t (("+-*/.<>=!?$%_&~^:" . "w")) beginning-of-defun
          (font-lock-mark-block-function . mark-defun))))

(defvar athena-mode-line-process "")

(defvar athena-mode-map nil
  "Keymap for Athena mode.
All commands in `lisp-mode-shared-map' are inherited by this map.")

(if athena-mode-map
    ()
  (let ((map (make-sparse-keymap "Athena")))
    (setq athena-mode-map
	  (nconc (make-sparse-keymap) lisp-mode-shared-map))
    (define-key athena-mode-map [menu-bar] (make-sparse-keymap))
    (define-key athena-mode-map [menu-bar athena]
      (cons "Athena" map))
    (define-key map [run-athena] '("Run Inferior Athena" . run-athena))
    (define-key map [uncomment-region]
      '("Uncomment Out Region" . (lambda (beg end)
                                   (interactive "r")
                                   (comment-region beg end '(4)))))
    (define-key map [comment-region] '("Comment Out Region" . comment-region))
    (define-key map [indent-region] '("Indent Region" . indent-region))
    (define-key map [indent-line] '("Indent Line" . lisp-indent-line))
    (put 'comment-region 'menu-enable 'mark-active)
    (put 'uncomment-region 'menu-enable 'mark-active)
    (put 'indent-region 'menu-enable 'mark-active)))

;; Used by cmuscheme
(defun athena-mode-commands (map)
  ;;(define-key map "\t" 'indent-for-tab-command) ; default
  (define-key map "\177" 'backward-delete-char-untabify)
  (define-key map "\e\C-q" 'indent-sexp))

;;;###autoload
(defun athena-mode ()
  "Major mode for editing Athena code.
Editing commands are similar to those of lisp-mode.

In addition, if an inferior Athena process is running, some additional
commands will be defined, for evaluating expressions and controlling
the interpreter, and the state of the process will be displayed in the
modeline of all Athena buffers.  The names of commands that interact
with the Athena process start with \"xathena-\".  For more information
see the documentation for xathena-interaction-mode.

Commands:
Delete converts tabs to spaces as it moves back.
Blank lines separate paragraphs.  Sharp-signs start comments.
\\{athena-mode-map}
Entry to this mode calls the value of athena-mode-hook
if that value is non-nil."
  (interactive)
  (kill-all-local-variables)
  (athena-mode-initialize)
  (athena-mode-variables)
  (run-hooks 'athena-mode-hook))

(defun athena-mode-initialize ()
  (use-local-map athena-mode-map)
  (setq major-mode 'athena-mode)
  (setq mode-name "Athena"))

(defgroup athena nil
  "Editing Athena code"
  :group 'lisp)

(defcustom athena-mit-dialect t
  "If non-nil, athena mode is specialized for MIT Athena.
Set this to nil if you normally use another dialect."
  :type 'boolean
  :group 'athena)

(defcustom dsssl-sgml-declaration
  "<!DOCTYPE style-sheet PUBLIC \"-//James Clark//DTD DSSSL Style Sheet//EN\">
"
  "*An SGML declaration for the DSSSL file.
If it is defined as a string this will be inserted into an empty buffer
which is in dsssl-mode.  It is typically James Clark's style-sheet
doctype, as required for Jade."
  :type '(choice (string :tag "Specified string") 
                 (const :tag "None" :value nil))
  :group 'athena)

(defcustom athena-mode-hook nil
  "Normal hook (list of functions) run when entering athena-mode.
See `run-hooks'."
  :type 'hook
  :group 'athena)

(defcustom dsssl-mode-hook nil
  "Normal hook (list of functions) run when entering dsssl-mode.
See `run-hooks'."
  :type 'hook
  :group 'athena)

(defvar dsssl-imenu-generic-expression
  ;; Perhaps this should also look for the style-sheet DTD tags.  I'm
  ;; not sure it's the best way to organize it; perhaps one type
  ;; should be at the first level, though you don't see this anyhow if
  ;; it gets split up.
  '(("Defines" 
     "^(define\\s-+(?\\(\\sw+\\)" 1)
    ("Modes"
     "^\\s-*(mode\\s-+\\(\\(\\sw\\|\\s-\\)+\\)" 1)
    ("Elements"
     ;; (element foo ...) or (element (foo bar ...) ...)
     ;; Fixme: Perhaps it should do `root'.
     "^\\s-*(element\\s-+(?\\(\\(\\sw\\|\\s-\\)+\\))?" 1)
    ("Declarations" 
     "^(declare\\(-\\sw+\\)+\\>\\s-+\\(\\sw+\\)" 2))
  "Imenu generic expression for DSSSL mode.  See `imenu-generic-expression'.")

(defconst athena-font-lock-keywords-1
  (eval-when-compile
    (list
     ;;
     ;; Declarations.  Hannes Haug <hannes.haug@student.uni-tuebingen.de> says
     ;; this works for SOS, STklos, SCOOPS, Meroon and Tiny CLOS.
     (list (concat "(\\(define\\*?\\("
		   ;; Function names.
		   "\\(\\|-public\\|-method\\|-generic\\(-procedure\\)?\\)\\|"
		   ;; Macro names, as variable names.  A bit dubious, this.
		   "\\(-syntax\\)\\|"
		   ;; Class names.
		   "-class"
                   ;; Guile modules.
                   "\\|-module"
		   "\\)\\)\\>"
		   ;; Any whitespace and declared object.
		   "[ \t]*(?"
		   "\\(\\sw+\\)?")
	   '(1 font-lock-keyword-face)
	   '(6 (cond ((match-beginning 3) font-lock-function-name-face)
		     ((match-beginning 5) font-lock-variable-name-face)
		     (t font-lock-type-face))
	       nil t))
     ))
  "Subdued expressions to highlight in Athena modes.")

(defconst athena-font-lock-keywords-2
  (append athena-font-lock-keywords-1
   (eval-when-compile
     (list
      ;;
      ;; Control structures.
      (cons
       (concat
	"(" (regexp-opt
	     '("begin" "call-with-current-continuation" "call/cc"
	       "call-with-input-file" "call-with-output-file" "case" "cond"
	       "do" "else" "for-each" ; "if" "lambda" "method"
	       ; "let" "let*" "let-syntax" "letrec" "letrec-syntax"
	       ;; Hannes Haug <hannes.haug@student.uni-tuebingen.de> wants:
	       "and" "or" "delay"
	       ;; Stefan Monnier <stefan.monnier@epfl.ch> says don't bother:
	       ;;"quasiquote" "quote" "unquote" "unquote-splicing"
	       "map" "syntax" "syntax-rules") t)
	"\\>") 1)
      ;;
      ;; David Fox <fox@graphics.cs.nyu.edu> for SOS/STklos class specifiers.
      '("\\<<\\sw+>\\>" . font-lock-type-face)
      ;;
      ;; Athena `:' keywords as builtins.
      '("\\<:\\sw+\\>" . font-lock-builtin-face)
      )))
  "Gaudy expressions to highlight in Athena modes.")

(defvar athena-font-lock-keywords athena-font-lock-keywords-1
  "Default expressions to highlight in Athena modes.")

;;;###autoload
(defun dsssl-mode ()
  "Major mode for editing DSSSL code.
Editing commands are similar to those of lisp-mode.

Commands:
Delete converts tabs to spaces as it moves back.
Blank lines separate paragraphs.  Sharp-signs start comments.
\\{athena-mode-map}
Entering this mode runs the hooks `athena-mode-hook' and then
`dsssl-mode-hook' and inserts the value of `dsssl-sgml-declaration' if
that variable's value is a string."
  (interactive)
  (kill-all-local-variables)
  (use-local-map athena-mode-map)
  (athena-mode-initialize)
  (make-local-variable 'page-delimiter)
  (setq page-delimiter "^;;;" ; ^L not valid SGML char
	major-mode 'dsssl-mode
	mode-name "DSSSL")
  ;; Insert a suitable SGML declaration into an empty buffer.
  (and (zerop (buffer-size))
       (stringp dsssl-sgml-declaration)
       (not buffer-read-only)
       (insert dsssl-sgml-declaration))
  (athena-mode-variables)
  (setq font-lock-defaults '(dsssl-font-lock-keywords
			     nil t (("+-*/.<>=?$%_&~^:" . "w"))
			     beginning-of-defun
			     (font-lock-mark-block-function . mark-defun)))
  (setq imenu-case-fold-search nil)
  (setq imenu-generic-expression dsssl-imenu-generic-expression)
  (setq imenu-syntax-alist '(("+-*/.<>=?$%_&~^:" . "w")))
  (run-hooks 'athena-mode-hook)
  (run-hooks 'dsssl-mode-hook))

;; Extra syntax for DSSSL.  This isn't separated from Athena, but
;; shouldn't cause much trouble in athena-mode.
(put 'element 'athena-indent-function 1)
(put 'mode 'athena-indent-function 1)
(put 'with-mode 'athena-indent-function 1)
(put 'make 'athena-indent-function 1)
(put 'style 'athena-indent-function 1)
(put 'root 'athena-indent-function 1)

;; Inserted by DRM for Athena mode:

(put 'pick-any 'athena-indent-function 1)
(put 'pick-witness 'athena-indent-function 1)
(put 'pick-witnesses 'athena-indent-function 1)
(put 'dlet 'athena-indent-function 1)
(put 'dletrec 'athena-indent-function 1)
(put 'forall 'athena-indent-function 1)
(put 'exists 'athena-indent-function 1)
(put 'assume 'athena-indent-function 1)
(put 'assume-let 'athena-indent-function 1)
(put 'assert 'athena-indent-function 1)
(put 'method 'athena-indent-function 1)
(put 'function 'athena-indent-function 1)
(put 'match 'athena-indent-function 1)
(put 'dmatch 'athena-indent-function 1)
(put 'suppose-absurd 'athena-indent-function 1)
(put 'suppose-absurd-let 'athena-indent-function 1)
(put 'conclude 'athena-indent-function 1)
(put 'by-induction 'athena-indent-function 1)
(put 'datatype-cases 'athena-indent-function 1)
(put 'concrete 'athena-indent-function 1)
(put 'abstract 'athena-indent-function 1)
(put 'theory 'athena-indent-function 1)
(put 'evolve 'athena-indent-function 1)
(put 'axiom 'athena-indent-function 1)
(put 'extend 'athena-indent-function 1)
(put 'get 'athena-indent-function 1)
(put 'get-abstract 'athena-indent-function 1)
(put 'declare 'athena-indent-function 1)

(defvar dsssl-font-lock-keywords
  (eval-when-compile
    (list
     ;; Similar to Athena
     (list "(\\(define\\(-\\w+\\)?\\)\\>[ 	]*\\\((?\\)\\(\\sw+\\)\\>"
	   '(1 font-lock-keyword-face)
	   '(4 font-lock-function-name-face))
     (cons
      (concat "(\\("
	      ;; (make-regexp '("case" "cond" "else" "if" "lambda"
	      ;; "let" "let*" "letrec" "and" "or" "map" "with-mode"))
	      "and\\|c\\(ase\\|ond\\)\\|else\\|if\\|"
	      "l\\(ambda\\|et\\(\\|*\\|rec\\)\\)\\|map\\|or\\|with-mode"
	      "\\)\\>")
      1)
     ;; DSSSL syntax
     '("(\\(element\\|mode\\|declare-\\w+\\)\\>[ 	]*\\(\\sw+\\)"
       (1 font-lock-keyword-face)
       (2 font-lock-type-face))
     '("(\\(element\\)\\>[ 	]*(\\(\\S)+\\))"
       (1 font-lock-keyword-face)
       (2 font-lock-type-face))
     '("\\<\\sw+:\\>" . font-lock-constant-face) ; trailing `:' c.f. athena
     ;; SGML markup (from sgml-mode) :
     '("<\\([!?][-a-z0-9]+\\)" 1 font-lock-keyword-face)
     '("<\\(/?[-a-z0-9]+\\)" 1 font-lock-function-name-face)))
  "Default expressions to highlight in DSSSL mode.")


(defvar calculate-lisp-indent-last-sexp)

;; Copied from lisp-indent-function, but with gets of
;; athena-indent-{function,hook}.
(defun athena-indent-function (indent-point state)
  (let ((normal-indent (current-column)))
    (goto-char (1+ (elt state 1)))
    (parse-partial-sexp (point) calculate-lisp-indent-last-sexp 0 t)
    (if (and (elt state 2)
             (not (looking-at "\\sw\\|\\s_")))
        ;; car of form doesn't seem to be a a symbol
        (progn
          (if (not (> (save-excursion (forward-line 1) (point))
                      calculate-lisp-indent-last-sexp))
              (progn (goto-char calculate-lisp-indent-last-sexp)
                     (beginning-of-line)
                     (parse-partial-sexp (point)
					 calculate-lisp-indent-last-sexp 0 t)))
          ;; Indent under the list or under the first sexp on the same
          ;; line as calculate-lisp-indent-last-sexp.  Note that first
          ;; thing on that line has to be complete sexp since we are
          ;; inside the innermost containing sexp.
          (backward-prefix-chars)
          (current-column))
      (let ((function (buffer-substring (point)
					(progn (forward-sexp 1) (point))))
	    method)
	(setq method (or (get (intern-soft function) 'athena-indent-function)
			 (get (intern-soft function) 'athena-indent-hook)))
	(cond ((or (eq method 'defun)
		   (and (null method)
			(> (length function) 3)
			(string-match "\\`def" function)))
	       (lisp-indent-defform state indent-point))
	      ((integerp method)
	       (lisp-indent-specform method state
				     indent-point normal-indent))
	      (method
		(funcall method state indent-point normal-indent)))))))


;;; Let is different in Athena

(defun would-be-symbol (string)
  (not (string-equal (substring string 0 1) "(")))

(defun next-sexp-as-string ()
  ;; Assumes that protected by a save-excursion
  (forward-sexp 1)
  (let ((the-end (point)))
    (backward-sexp 1)
    (buffer-substring (point) the-end)))

;; This is correct but too slow.
;; The one below works almost always.
;;(defun athena-let-indent (state indent-point)
;;  (if (would-be-symbol (next-sexp-as-string))
;;      (athena-indent-specform 2 state indent-point)
;;      (athena-indent-specform 1 state indent-point)))

(defun athena-let-indent (state indent-point normal-indent)
  (skip-chars-forward " \t")
  (if (looking-at "[-a-zA-Z0-9+*/?!@$%^&_:~]")
      (lisp-indent-specform 2 state indent-point normal-indent)
    (lisp-indent-specform 1 state indent-point normal-indent)))

;; (put 'begin 'athena-indent-function 0), say, causes begin to be indented
;; like defun if the first form is placed on the next line, otherwise
;; it is indented like any other form (i.e. forms line up under first).

(put 'begin 'athena-indent-function 0)
(put 'case 'athena-indent-function 1)
(put 'delay 'athena-indent-function 0)
(put 'do 'athena-indent-function 2)
(put 'lambda 'athena-indent-function 1)
(put 'let 'athena-indent-function 'athena-let-indent)
(put 'let* 'athena-indent-function 1)
(put 'letrec 'athena-indent-function 1)
(put 'sequence 'athena-indent-function 0) ; SICP, not r4rs
(put 'let-syntax 'athena-indent-function 1)
(put 'letrec-syntax 'athena-indent-function 1)
(put 'syntax-rules 'athena-indent-function 1)


(put 'call-with-input-file 'athena-indent-function 1)
(put 'with-input-from-file 'athena-indent-function 1)
(put 'with-input-from-port 'athena-indent-function 1)
(put 'call-with-output-file 'athena-indent-function 1)
(put 'with-output-to-file 'athena-indent-function 1)
(put 'with-output-to-port 'athena-indent-function 1)
(put 'call-with-values 'athena-indent-function 1) ; r5rs?
(put 'dynamic-wind 'athena-indent-function 3) ; r5rs?

;;;; MIT Scheme specific indentation.

(if athena-mit-dialect
    (progn
      (put 'fluid-let 'athena-indent-function 1)
      (put 'in-package 'athena-indent-function 1)
      (put 'local-declare 'athena-indent-function 1)
      (put 'macro 'athena-indent-function 1)
      (put 'make-environment 'athena-indent-function 0)
      (put 'named-lambda 'athena-indent-function 1)
      (put 'using-syntax 'athena-indent-function 1)

      (put 'with-input-from-string 'athena-indent-function 1)
      (put 'with-output-to-string 'athena-indent-function 0)
      (put 'with-values 'athena-indent-function 1)

      (put 'syntax-table-define 'athena-indent-function 2)
      (put 'list-transform-positive 'athena-indent-function 1)
      (put 'list-transform-negative 'athena-indent-function 1)
      (put 'list-search-positive 'athena-indent-function 1)
      (put 'list-search-negative 'athena-indent-function 1)

      (put 'access-components 'athena-indent-function 1)
      (put 'assignment-components 'athena-indent-function 1)
      (put 'combination-components 'athena-indent-function 1)
      (put 'comment-components 'athena-indent-function 1)
      (put 'conditional-components 'athena-indent-function 1)
      (put 'disjunction-components 'athena-indent-function 1)
      (put 'declaration-components 'athena-indent-function 1)
      (put 'definition-components 'athena-indent-function 1)
      (put 'delay-components 'athena-indent-function 1)
      (put 'in-package-components 'athena-indent-function 1)
      (put 'lambda-components 'athena-indent-function 1)
      (put 'lambda-components* 'athena-indent-function 1)
      (put 'lambda-components** 'athena-indent-function 1)
      (put 'open-block-components 'athena-indent-function 1)
      (put 'pathname-components 'athena-indent-function 1)
      (put 'procedure-components 'athena-indent-function 1)
      (put 'sequence-components 'athena-indent-function 1)
      (put 'unassigned\?-components 'athena-indent-function 1)
      (put 'unbound\?-components 'athena-indent-function 1)
      (put 'variable-components 'athena-indent-function 1)))

(provide 'athena)

;;; athena.el ends here
