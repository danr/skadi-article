\documentclass{sigplanconf}
%include polycode.fmt
%format BoolSym = "\mathit{Bool}^\dagger"
%format ListSym = "\mathit{List}^\dagger"
%format FalseSym = "\mathit{false}^\dagger"
%format TrueSym = "\mathit{true}^\dagger"
%format c1
%format c2
%format ma1
%format ma2
%format a1
%format a2
%format /\ = "\wedge"
%format \/ = "\vee"
%format ==> = "\Rightarrow"
%format <=> = "\Leftrightarrow"
%format nt = "\neg"
%format === = "\Longleftrightarrow"
%format ExprSym = "\mathit{Expr}^\dagger"
%format TypeSym = "\mathit{Type}^\dagger"
%format sel1
%format sel2
%format sel3
%format P1
%format P2
%format P3
%format P4
%format //- = "\!"
%format >>> = "\rhd"
%format ¤ = "\phantom"
%format /// = "\;\;\;"
%format //  = "\;"
%format x1
%format x2
%format b1
%format b2
%format pSym = "\mathit{p}^\dagger"
%format ASym = "\mathit{A}^\dagger"
%format BSym = "\mathit{B}^\dagger"
%format x1
%format xn = "\mathit{x}_n"
%format e1
%format en = "\mathit{e}_n"
%format s1
%format sn = "\mathit{s}_n"
%format K1
%format Kn = "\mathit{K}_n"
%format (transr (e)) = "\llbracket" e "\rrbracket\!\!\!\Rightarrow\!\!\!"
%format (trans (e))  = "\llbracket" e "\rrbracket"
%format isK1 = "\mathit{isK}_1"
%format isKn = "\mathit{isK}_n"
%format ++? = ++"\!^\dagger"
%format ==? = =="^\dagger"
%format undefined = "\bot"
%format fSym = "\mathit{f}^\dagger"
%format mdo = "\mathbf{mdo}"
%format x_1
%format x_2
%format x_3
%format x_n
%format y_1
%format y_2
%format y_3
%format y_m
%format :-> = ":\rightarrow"
%format env = "\rho"
%format :+: = ":\!\!+\!\!:"
%format :&: = ":\!\&\!:"
%format :>: = ":>:"
%format .>. = ".\!>\!\!."
%format Meps = "\epsilon"
%format (repp (p) (i) (j)) = p "\!\{" i "," j "\}"
%format (reppp (p) (i) (j)) = "(" p ")\!\{" i "," j "\}"
%format (maxx (i) (j)) = i "\cap" j
%format (minn (i) (j)) = i "\cup" j
%format Mempset = "\emptyset"
%format ==> = "\Longrightarrow"





%-----------------------------------------------------------------------------
%
%               Template for sigplanconf LaTeX Class
%
% Name:         sigplanconf-template.tex
%
% Purpose:      A template for sigplanconf.cls, which is a LaTeX 2e class
%               file for SIGPLAN conference proceedings.
%
% Guide:        Refer to "Author's Guide to the ACM SIGPLAN Class,"
%               sigplanconf-guide.pdf
%
% Author:       Paul C. Anagnostopoulos
%               Windfall Software
%               978 371-2316
%               paul@windfall.com
%
% Created:      15 February 2005
%
%-----------------------------------------------------------------------------



% The following \documentclass options may be useful:

% preprint      Remove this option only once the paper is in final form.
% 10pt          To set in 10-point type instead of 9-point.
% 11pt          To set in 11-point type instead of 9-point.
% authoryear    To obtain author/year citation style instead of numeric.

\usepackage{amsmath}
\usepackage{xcolor}
\usepackage{graphicx}
\usepackage{textcomp}

\newcommand{\comment}[1]{\emph{COMMENT: #1}}
\newcommand{\ifthenelse}{|if|-|then|-|else|}
%format § = $

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{ICFP '15}{September, 2015, Vancouver, Canada}
\copyrightyear{2015}
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
\doi{nnnnnnn.nnnnnnn}

% Uncomment one of the following two, if you are not going for the
% traditional copyright transfer agreement.

%\exclusivelicense                % ACM gets exclusive license to publish,
                                  % you retain copyright

%\permissiontopublish             % ACM gets nonexclusive license to publish
                                  % (paid open-access papers,
                                  % short abstracts)

\titlebanner{DRAFT}        % These are ignored unless
\preprintfooter{}   % 'preprint' option specified.

\title{SAT-based Bounded Model Checking\\for Functional Programs}
\subtitle{}

\authorinfo{Koen Claessen \and Dan Ros{\'e}n}
           {Chalmers University of Technology}
           {\{koen,danr\}@@chalmers.se}

\maketitle

%% DO THIS FOR THE FINAL VERSION!!!
%\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
%\terms
%bounded model checking, SAT

%include Abstract.lhs

% ------------------------------------------------------------------------------

%include Introduction.lhs

% ------------------------------------------------------------------------------

%include Content.lhs

% ------------------------------------------------------------------------------

%include ExamplesExperiments.lhs

% ------------------------------------------------------------------------------

%include RelatedWork.lhs

% ------------------------------------------------------------------------------

%\setcounter{section}{7}
%include DiscussionConclusion.lhs

% ------------------------------------------------------------------------------

%\appendix
%\section{Appendix Title}

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}
\bibliography{Paper}

% The bibliography should be embedded for final submission.

%\begin{thebibliography}{}
%\softraggedright

%\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
%P. Q. Smith, and X. Y. Jones. ...reference text...

%\end{thebibliography}


\end{document}

