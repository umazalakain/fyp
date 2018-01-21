\documentclass[12pt,a4paper]{report}


% This handles the translation of unicode to latex:
\usepackage[utf8]{inputenc}
% \usepackage{autofe}

% The following packages are needed because unicode is translated (using the
% next set of packages) to latex commands. You may need more packages if you use
% more unicode characters:

\usepackage{amssymb}
% \usepackage{bbm}
\usepackage[english]{babel}


% Title options

% \subject{Submitted for the Degree of B.Sc. in Computer Science}
\title{Evidence providing problem solvers in Agda}
\author{Uma Zalakain}
\date{March 2018}

\begin{document}

\begin{titlepage}
    \centering{}

    {\scshape\LARGE University of Strathclyde \par}
    \vspace{1cm}

    {\scshape\Large Submitted for the Degree of B.Sc. in Computer Science \par}
    \vspace{1.5cm}

    {\huge\bfseries Evidence providing problem solvers in Agda \par}
    \vspace{2cm}

    {\Large\itshape Uma Zalakain\par}
    \vfill

    supervised by\par
    Dr. Conor \textsc{McBride}

    \vfill

    {\small
    Except where explicitly stated all the work in this report, including
    appendices, is my own and was carried out during my final year. It has not
    been submitted for assessment in any other context.
    }

    \vfill

    {\large \today \par}
\end{titlepage}


\newpage

%   Introductory Pages Before the chapters of your report, there should be a
%   number of introductory pages. These should include:
%   - the title page (which has a compulsory format),
%   - a page giving an abstract of your work,
%   - an acknowledgements page, and
%   - a table of contents.

- Proving certain theorems can be boring and we want to automate it
- We don't want just the answer, we want a proof that it is the correct answer

\section{Introduction}

%   Introduction This should briefly describe the problem which you set out to
%   solve and should essentially summarise the rest of your report. The aim of
%   an introduction is to convince the reader that they should read on, so it is
%   very important that excessive detail is avoided at this stage.

- What Agda is
- How Agda works as a proof assistant
- Types as propositions
- What a solver is
- Presburger arithmetic as an interesting goal

%   The introduction should include the list of objectives that you identified
%   for the project, as well as a brief overview of the outcome. In its final
%   part, the introduction will usually outline the structure of the rest of the
%   report.

- Better understand theorem proving in Agda
- Write something that can be useful for others to use

\section{Related work}

%   Related Work You should survey and critically evaluate other work which you
%   have read or otherwise considered in the general area of the project topic.
%   The aim here is to place your project work in the context of the related
%   work.

\subsection{Monoid solver}

- What is a Monoid?
- Canonical forms and evaluation homomorphism
- Lists are free monoids

\subsection{Commutative ring solver}

- What is a commutative ring?
- Horner normal form + constraints

\section{Problem description and specification}

%   Problem Description and Specification Describe in detail, with examples if
%   appropriate, the problem which you are trying to solve. You should clearly
%   and concisely specify the problem and should say how the specification was
%   arrived at. You should also provide a general discussion of your approach to
%   solving the project problem.

- What Presburger arithmetic is
- The three ways of solving it
- What ways we chose, and why
- How to do this in Agda, what the benefits are

%   As part of this chapter – or more likely in a related appendix – you should
%   also normally include the original plan which was submitted as part of your
%   Project Specification and Plan deliverable in the first semester. You should
%   not, however, be particularly concerned if your project deviated slightly
%   from this plan.

\section{System design}

- High level plan of the module
    - Representation
    - Normalisation
    - Simplification
    - Correctness proofs
    - Quoting

%   System Design In this chapter, you should describe how the project was
%   designed. You should include discussions of the design method, design
%   process, and final design outcome. This is where you include the high level
%   description of the architecture of your project's product and, if
%   appropriate, the design of the user interface and data management.

\section{Detailed design and implementation}

%   Detailed Design and Implementation In this chapter you should describe your
%   design in more detail, taking the most interesting aspects right down to the
%   implementation details. You should include detailed design decisions and
%   trade-offs considered and made, such as the selection of algorithms, data
%   structures, implementation languages, and appropriate tools to support the
%   development process. It should also include your justifications for these
%   choices. In addition, you should describe how you have tried to address
%   relevant qualities of the product produced, such as maintainability,
%   reliability, and user-friendliness. It is not necessary to describe every
%   aspect of your system in excruciating detail, but you should describe each
%   in enough detail that the reader of your report can understand the overall
%   project, and you should thoroughly discuss the most demanding and
%   interesting aspects of your design and implementation.

- The source code itself, minus the boring bits
- Things from agda-stdlib in the abstract?

\section{Verification and validation}

%   Verification and Validation In this section you should outline the
%   verification and validation procedures that you've adopted throughout the
%   project to ensure that the final product satisfies its specification. In
%   particular, you should outline the test procedures that you adopted during
%   and after implementation. Your aim here is to convince the reader that the
%   product has been thoroughly and appropriately verified. Detailed test
%   results should, however, form a separate appendix at the end of the report.

- Why is this absolutely correct, Agda?

\section{Results and evaluation}

%   Results and Evaluation The aim of this chapter is twofold. On one hand, it
%   aims to present the final outcome of the project – i.e., the system
%   developed – in an appropriate way so that readers of your report can form a
%   clear picture of the system operation and provided functionality without the
%   need for a live demo. This would normally require the inclusion of
%   screenshots and/or images of the system in operation, and indicative results
%   generated by the system. On the other hand, this chapter also aims to
%   present an appropriate evaluation of the project as whole, both in terms of
%   the outcome and in terms of the process followed.

%   The evaluation of the outcome is expected to be primarily evidence-based,
%   i.e., the result of either an experimental process, like usability tests and
%   evaluations, performance-related measurements, etc., or a formal analysis,
%   such as algorithmic and mathematical analysis of system properties, etc. The
%   precise nature of the evaluation will depend on the project requirements.
%   Please note that if you intend to carry out usability tests, you will need
%   to first obtain approval from the Department's Ethics Committee - the
%   section on Evaluation and Ethics Approval provides further detail.

%   The evaluation of the process is expected to be primarily a reflective
%   examination of the planning, organisation, implementation and evaluation of
%   the project. This will normally include the lessons learnt and explanations
%   of any significant deviations from the original project plan.

\section{Summary and conclusions}

%   Summary and Conclusions In the final chapter of your report, you should
%   summarise how successful you were in achieving the original project
%   objectives, what problems arose in the course of the project which could not
%   be readily solved in the time available, and how your work could be
%   developed in future to enhance its utility. It is OK to be upbeat,
%   especially if you are pleased with what you have achieved!

\section{Bibliography}

%   References/Bibliography The references should consist of a list of papers
%   and books referred to in the body of your report. These should be formatted
%   as for scholarly computer science publications. Most text- and word-
%   processors provide useful assistance with referencing - for example latex
%   uses bibtex. As you know, there are two principal reference schemes.

%       In one, the list is ordered alphabetically on author's surname and
%       within the text references take the form (Surname, Date). For example, a
%       reference to a 2014 work by Zobel would be written (Zobel, 2014).

%       In the other, the list is ordered in the sequence in which a reference
%       first appears in the report.

%   For both schemes, each reference in the reference list should contain the
%   following information: author, title, journal or publisher (if book), volume
%   and part, and date. Depending of the style of references you use, Zobel's
%   2014 book might be listed in the references of your report as follows:

%   Justin Zobel. Writing for Computer Science. Springer-Verlag, 2014.

%   For more examples of the first style, see the way in which references are
%   laid out in "Software Engineering: A Practitioner's Approach" by Roger
%   Pressman. Note carefully that your references should not just be a list of
%   URLs! Web pages are not scholarly publications. In particular, they are not
%   peer reviewed, and so could contain erroneous or inaccurate information.

\section{Appendices}

%   Appendix A - Detailed Specification and Design This appendix should contain
%   the details of your project specification that were not included in the main
%   body of your report.

%   Appendix B - Detailed Test Strategy and Test Cases This appendix should
%   contain the details of the strategy you used to test your software, together
%   with your tabulated and commented test results.

%   Appendix C - User Guide This appendix should provide a detailed description
%   of how to use your system. In some cases, it may also be appropriate to
%   include a second guide dealing with maintenance and updating issues.

\end{document}
