#  Loop Analyst.py
# coding=utf8
#  LoopAnalystX
#
#  Created by Alexis Dinno on 6/18/06.
#  Copyright (c) 2006-2016 Alexis Dinno. All rights reserved.
#

import wx
from base64 import b64decode
from wx.aui import AuiNotebook, EVT_AUINOTEBOOK_PAGE_CHANGED
from tempfile import gettempdir
from sys import argv
from os import system, remove, getcwd
from os.path import exists, split, realpath
from cPickle import load, dump
from numpy import array, sign, dot
from copy import copy, deepcopy
from fpformat import fix
from string import lower
from cStringIO import StringIO
from zlib import decompress
from wx import ImageFromStream, BitmapFromImage, EmptyIcon

################################################################################
### CLASSES FOR COMMUNITY MATRICES AND RELATED OBJECTS                       ###
################################################################################

class PERSISTENT:
    """A collection of preferences settings saved to a file and loaded on restarting the program.

Persistent Objects
0: RecentDirectory -- The most recently opened or saved directory 
1: RecentLibraries -- The most recently opened or saved libraries
2: RecentLibrariesListLength -- The number of recent libraries that are 
   tracked
3: GraphColoring -- Whether graphs are rendered in black and white (0), 
   greyscale (2), or color (3)
4: DisplayFontSize -- Size of the font used in the analytic tables
5: WeightedPredictionThreshold -- Threshold value at which to represent a 
   disambiguated prediction
6: ThresholdCriterion -- Whether the weighted prediction threshold is taken 
   as strictly greater than ">" (0), or greater than or equal to ">=" (1)
7: Position -- Window position at last quit
8: Size -- Window size at last quit
9: WeightedFeedbackPrecision -- Number of places to the right of the decimal point in a WFM.
10: dotLocation -- path to graphviz's dot command
11: Language -- Internationalization preference"""

# Default PERSISTENT values
    Persistence = [None, None, 5, 0, 24, .5, 1, (0, 22), (1078,600), 1, "", 0]
    
##########
# Class for GLOBAL variables
class GLOBAL:
  
    # Localization
    # get path to Loop Analyst.py
    LApath = split(realpath(__file__))[0]

    # load the language internationalization, default English (US)
    if exists(LApath+'/localizations/en-us.localization'):
        language = load(file(LApath+'/localizations/en-us.localization',"r"))

    # Load image data
    # load the icon data
    if exists(LApath+'/IconData.b64'):
        IconData = load(file(LApath+'/IconData.b64',"r"))

    # load the splash data
    if exists(LApath+'/SplashData.b64'):
        SplashData = load(file(LApath+'/SplashData.b64',"r"))

    # Constants of various and sundry types
    CM_Colors = ["#8000BF","#0000BF","#00BF00","#BF0000","#808000","#FF8000","#8000FF","#0080FF","#008080","#BFBF80","#BF8000","#FF00FF","#804080","#004080","#408040","#FEFE00","#FFBF00","#804040","#8080FF","#000080","#004000","#BFBF00","#FF8080","#FF0080","#400040","#404080","#BFFF00","#FFFFBF","#FFBF80","#FF0000"]

    # try to identify PATH/dot
#    if exists("/usr/local/bin/dot"):
#        dotLocation = "/usr/local/bin/dot"
#    elif exists("/opt/local/bin/dot"): 
#        dotLocation = "/opt/local/bin/dot"
#    else:
#        dotLocation = ""

    dotLocation = "/usr/bin/dot"
    # CommunityMatrix related objects
    N = None
    Term = []
    LTerm = []
    LOVE = []
    LLOVE = []
    incomplete = True
    LOP = []
    LOL = []
    MOSL = []
    PLOS = []
    N_MOSL = None
    CCM = []
    x = None
    Valid = True

    # CMLibrary Related objects
    Library = None
    LibraryName = language["main_GLOBALLibraryName"][0]
    CMNameClip = ""
    CMDataClip = ""
    Cache = []
    LibraryLastSaved = None

    # EditCM Related Objects
    Editindex = None
    EditA = ""
    EditName = ""
    EditNames = ""
    
    # Clipboard Related Objects
    ClipCM = ""
    ClipGraph = None

    # History Related Objects
    History = []
    HistoryIndex = 0

    # Persistent Objects
    RecentDirectory = ""              #PERSISTENCE[0]
    RecentLibraries = []              #PERSISTENCE[1]
    RecentLibrariesListLength = 10    #PERSISTENCE[2]
    GraphColoring = 0                 #PERSISTENCE[3]
    DisplayFontSize = 24              #PERSISTENCE[4]
    WeightedPredictionThreshold = .5  #PERSISTENCE[5]
    ThresholdCriterion = 1            #PERSISTENCE[6]
    Position = (0, 22)                #PERSISTENCE[7]
    Size = (1078, 600)                #PERSISTENCE[8]
    WeightedFeedbackPrecision = 1     #PERSISTENCE[9]
    dotLocation = dotLocation         #PERSISTENCE[10]
    Language = 0                      #PERSISTENCE[11]
    pass

##########
# Class for community matrix
class CommunityMatrix:
    def __init__(self,A=None,name=GLOBAL.language["main_CMName"][0],names=None, Graph = "", GraphFlag = False, CEMFlag = False, CorrelationsFlag = False, LoopsFlag = False, PathsFlag = False, WFMFlag = False, AdjointFlag = False, WPMFlag = False, CLEMFlag = False):
        """Construct a CommunityMatrix object and initialize its variables; return a CommunityMatrix instance."""

        def Unique(intlist):
            """Compute unique values in a list of integers; return a list"""
            if len(intlist) == 0:
                return []
            elements = {}
            for x in intlist:
                elements[x] = 1
            return elements.keys()
        
        def IsPath(j):
            """Test that GLOBAL.LOVE terminates in j; return a boolean"""
            if (GLOBAL.LOVE[-1:] == [j]):
                return(True)
            return(False)

        def MakeENVY():
            """Compute from A and GLOBAL.LOVE which Elements are Not Visited Yet; returns a list"""
            ENVY = []
            for x in range(0,GLOBAL.N):
                if A[x][GLOBAL.LOVE[-1]] != 0:
                    if GLOBAL.Term[x][GLOBAL.LOVE[-1]] == 0:
                        ENVY = ENVY+[x]
            ENVY = [element for element in ENVY if element not in GLOBAL.LOVE]
            return ENVY
                    
        def UpdateTerm():
            """Clear rows in GLOBAL.Term of any elements not in GLOBAL.LOVE; modify GLOBAL.Term"""
            for x in range(0,len(A)):
                if x not in GLOBAL.LOVE:
                    for y in range(0,len(A)):
                        GLOBAL.Term[y][x] = 0

        def SearchStep(i,j):
            """Compute and compile a List of Paths paths to j in A; modify GLOBAL.LOP"""
            ENVY = MakeENVY()
            # when there are no unvisited elements & GLOBAL.LOVE has more than 1 element, 
            # terminate the last element of GLOBAL.LOVE for the second to last element of 
            # GLOBAL.LOVE.
            if len(ENVY) == 0:
                if len(GLOBAL.LOVE) == 1:
                    GLOBAL.Term[GLOBAL.LOVE[-1]][GLOBAL.LOVE[-1]] = 1
                if len(GLOBAL.LOVE) > 1:
                    GLOBAL.Term[GLOBAL.LOVE[-1]][GLOBAL.LOVE[-2]] = 1
                GLOBAL.LOVE = GLOBAL.LOVE[:-1]
                UpdateTerm()
                # exit SearchStep if the last element of GLOBAL.LOVE is i & i is terminated
                # or if GLOBAL.LOVE is empty and return List Of Paths (GLOBAL.LOP)
                if len(GLOBAL.LOVE) == 0:
                    GLOBAL.incomplete = False
                if len(GLOBAL.LOVE) == 1:
                    test = False
                    for val in [x for x in range(0,len(A)) if x != i]:
                        if GLOBAL.Term[val][i] == 1:
                            test = True
                    if test:
                        return
                    
                    for x in range(0,len(N)):
                        GLOBAL.Term[x][GLOBAL.LOVE[-1]] = 1
                    GLOBAL.LOVE = GLOBAL.LOVE[:-1]
                    UpdateTerm()
                    GLOBAL.incomplete = False
            else:
                # append the first element (breadthwise search) of ENVY to GLOBAL.LOVE
                GLOBAL.LOVE = GLOBAL.LOVE+[ENVY[0]]
                # test whether new GLOBAL.LOVE is a path from i to j and respond accordingly
                if IsPath(j):
                    GLOBAL.LOP = list(GLOBAL.LOVE)
                    GLOBAL.LOVE = GLOBAL.incomplete = False
            return
            # end SearchStep()

        def OnePath(i,j):
            """Compute the first path in CM from i to j in a depth-first search; return a list"""
            # initialize search termination matrix
            GLOBAL.Term = [ [0]*len(A) for row in range(len(A)) ]
            
            # initialize list of paths (GLOBAL.LOP), list of visited elements (GLOBAL.LOVE)
            GLOBAL.LOP = []
            GLOBAL.LOVE = [i]
            
            GLOBAL.incomplete = True
            while (GLOBAL.incomplete):
                SearchStep(i,j)
            return(GLOBAL.LOP)
            # end OnePath()

        def IsIsolated():
            """Test if there is no simple path from any element to any other element; return a boolean"""
            reached_elements = []
            reaching_elements = []
            for x in range(1,len(A)):
                if (not(x in reached_elements)):
                    # list of paths from 0 to elements 1 to N-1
                    path = OnePath(0,x)
                    reached_elements = reached_elements+path[1:]
                if (not(x in reaching_elements)):
                    # list paths from elements 1 to N-1 to 0
                    path = OnePath(x,0)
                    reaching_elements = reaching_elements+path[:-1]
            return not(len(Unique(reached_elements)) == len(A)-1) or not(len(Unique(reaching_elements)) == len(A)-1)
            # end IsIsolated()

        def ValidateCM(CM):
            """Validate community matrix data by:\n  testing that it is square,\n  has only elements of -1, 0 or 1, and\n  has at least two parameters.\nProduce an error message these tests, fail, and return nothing otherwise."""
            
            # Is CM big enough?
            if (GLOBAL.N < 2):
                alert = wx.MessageDialog(frame, GLOBAL.language["main_CMDataSizeAlert"][0][0],GLOBAL.language["main_CMDataSizeAlert"][0][1], wx.OK)
                alert.ShowModal() # Shows it
                alert.Bind(wx.EVT_CHAR_HOOK, None)
                return False
            
            # Is CM a matrix? a square matrix?
            for i in range(0,GLOBAL.N):
                if not (GLOBAL.N == len(CM[i])):
                    alert = wx.MessageDialog(frame, GLOBAL.language["main_CMDataSquareAlert"][0][0],GLOBAL.language["main_CMDataSquareAlert"][0][1], wx.OK)
                    alert.ShowModal() # Shows it
                    alert.Bind(wx.EVT_CHAR_HOOK, None)
                    return False
            
            # Does CM contain only values = 1, 0 or -1?
            for i in range(0,GLOBAL.N):
                for j in range(0,GLOBAL.N):
                    if ( not ( (CM[i][j] == 1) or (CM[i][j] == 0) or (CM[i][j] == -1) ) ):
                        alert = wx.MessageDialog(frame, GLOBAL.language["main_CMDataValueAlert"][0][0],GLOBAL.language["main_CMDataValueAlert"][0][1], wx.OK)
                        alert.ShowModal() # Shows it
                        alert.Bind(wx.EVT_CHAR_HOOK, None)
                        return False
            
            # Is CM matrix is fully specified?
            # possibly replace with "if not 0 in self.A"
            zeros_present = False
            for i in range(0,GLOBAL.N):
                if (0 in CM[i]):
                    zeros_present = True
            if not zeros_present:
                alert = wx.MessageDialog(frame, GLOBAL.language["main_CMDataFullySpecifiedAlert"][0][0],GLOBAL.language["main_CMDataFullySpecifiedAlert"][0][1], wx.OK)
                alert.ShowModal() # Shows it
                alert.Bind(wx.EVT_CHAR_HOOK, None)
                return False
            
            # Is a subsystem of the matrix isolated?
            if IsIsolated():
                alert = wx.MessageDialog(frame, GLOBAL.language["main_CMDataIsolatedSubsystemAlert"][0][0],GLOBAL.language["main_CMDataIsolatedSubsystemAlert"][0][1], wx.OK)
                alert.ShowModal() # Shows it
                alert.Bind(wx.EVT_CHAR_HOOK, None)
                return False
                
            # Is the name list of an appropriate size?
            if names != None:
                if len(CM) != len(names):
                    alert = wx.MessageDialog(frame, GLOBAL.language["main_CMNameListAlert"][0][0],GLOBAL.language["main_CMNameListAlert"][0][1], wx.OK)
                    alert.ShowModal() # Shows it
                    alert.Bind(wx.EVT_CHAR_HOOK, None)
                    return False
            
            return True
            # end ValidateCM()
        
        # Set N = the size of CM
        GLOBAL.N = len(A)
        
        # Validate
        if ValidateCM(A) == False:
            self.A = []
            return

        # Class variables
        self.A = array(A, dtype='intp')
        self.Data = deepcopy(A)
        self.name = name
        self.names = names
        self.CMCache = []
        
        self.N = len(self.A)
        
        # Set up the objects to store calculated results and the flags to 
        # indicate whether they've been calculated and stored.
        self.Graph = None
        self.Graphed = None
        self.GraphFlag = False
        self.CEM = None
        self.Correlations = None
        self.Loops = None
        self.Paths = deepcopy(A)
        for i in range(0,self.N):
            for j in range(0,self.N):
                self.Paths[i][j] = None
        self.CEMFlag = False
        self.CorrelationsFlag = False
        self.LoopsFlag = False
        self.PathsFlag = False
        self.Adjoint = None
        self.AdjointFlag = False
        self.T = None
        self.TFlag = False
        self.WFM = None
        self.WFMFlag = False
        self.WPM = None
        self.WPMFlag = False
        self.CLEMFlag = False

        # create default variable names
        if self.names == None:
            from string import ascii_uppercase
            self.names = list(ascii_uppercase[0:GLOBAL.N])
        
    def __repr__(self):
        """Format the CommunityMatrix input for ascii representation; return a string."""
        OUTPUT = "["+str(self.A)+", "+str(self.name)+", "+str(self.names)+"]"
        return OUTPUT

    def LongestNameLen(self):
        """Compute the length of the longest variable name in self.names; return an integer."""
        length = 0
        for i in range(0,len(self.names)):
            if len(self.names[i]) > length:
                length = len(self.names[i])
        return length

    def __str__(self):
        """Format the CommunityMatrix input for ascii printing; return a string."""

        def CMRep(a_ij):
            """Format an element of the CommunityMatrix data for ascii printing; return a string."""
            if a_ij == 1:
                rep = ColFormat % ("+")
            if a_ij == 0:
                rep = ColFormat % ("0")
            if a_ij == -1:
                rep = ColFormat % ("-")
            return rep
        
        length = self.LongestNameLen()
        Format = "%-"+str(length)+"s "
        OUTPUT = Format % " "
        for i in range(0,self.N):
            ColFormat = "%-"+str(len(self.names[i]))+"s "
            OUTPUT = OUTPUT+ColFormat % self.names[i]
        OUTPUT = OUTPUT+"\n"
        for i in range(0,self.N):
            OUTPUT = OUTPUT+Format % (self.names[i])
            for j in range(0,self.N):
                value = CMRep(self.A[i,j])
                OUTPUT = OUTPUT+value
            if i < self.N-1:
                OUTPUT = OUTPUT+"\n"
        return OUTPUT

    ##########
    # FUNCTION: DisplayCM
    def DisplayCM(self):
        """Format the CM for ascii text display; return a string"""
        def CMRep(a_ij):
            """Format an element of the CommunityMatrix data for ascii printing; return a string."""
            if a_ij == 1 or a_ij == "+":
                return "+"
            if a_ij == -1 or a_ij == "-" or a_ij == "-":
                return "-"
            if a_ij == 0 or a_ij == "0":
                return "0"
        
        N = self.N
        
        # Set up the Spacers information and table width
        #    Spacers[0] are the variable names
        #    Spacers[1] are the lengths of the variable names
        #    Spacers[2] are the column 1 offsets for each variable
        #    Spacers[3] are the left-side offsets for each Adjoint element
        #    Spacers[4] are the right-side offsets for each Adjoint element
        MinSpace = 1
        Spacers = [copy(self.names),range(0,N), range(0,N), range(0,N), range(0,N)]
        Col1Width = self.LongestNameLen()
        TableWidth = Col1Width
        for i in range(0,N):
            Spacers[1][i] = len(Spacers[0][i])
            if Spacers[1][i] < MinSpace:
                Spacers[1][i] = MinSpace
            TableWidth = TableWidth + Spacers[1][i] + 1
            Spacers[2][i] = Col1Width - Spacers[1][i]
            Spacers[3][i] = Spacers[1][i]/2 + Spacers[1][i]%2 -1
            Spacers[4][i] = Spacers[1][i]/2
            
        if TableWidth < len(self.name)+Col1Width*len(self.names):
            TableWidth = len(self.name)+Col1Width*len(self.names)
        TableWidth = max(TableWidth,(len(self.name)),len("Community Matrix"))
        # Output will be written to Output
        Output = " "*TableWidth+"\n"
        
        # Create the title
        Output = Output+"Community Matrix\n"+str(self.name)+"\n\n"

        # Create the column headings
        Output = Output + " "*Col1Width
        for VarName in Spacers[0]:
            NewVarName = ""
            for index in range(0,len(VarName)):
                if VarName[index] != "\n":
                    NewVarName = NewVarName+VarName[index]
                else:
                    NewVarName = NewVarName+" "
            Output = Output + " " + NewVarName
        Output = Output + "\n"
        
        # Create row headings and populate rows
        for i in range(0,N):
        
            # translate line breaks into spaces
            NewVarName = ""
            for index in range(0,len(Spacers[0][i])):
                if Spacers[0][i][index] != "\n":
                    NewVarName = NewVarName+Spacers[0][i][index]
                else:
                    NewVarName = NewVarName+" "
            
            # get on with writing out the rows . . .
            Output = Output + " "*Spacers[2][i] + NewVarName
            for j in range(0,N):
                Output = Output + " "+ " "*Spacers[3][j] + CMRep(self.A[i,j]) + " "*Spacers[4][j]
            Output = Output + "\n"
        
        return Output


    ##########
    # FUNCTION: DisplayPaths
    def DisplayPaths(self):
        """Return the paths formatted for ascii display"""
        def IndexList(A, B):
            out = []
            for i in B:
                out = out+[A[i]]
            return out
            
        def PathRep(Pathsij):
            Output = ""
            for index in range(0,len(Pathsij)):
                Output = Output+"\t\t"+str(IndexList(self.names,Pathsij[index]))[1:-1].replace(", "," -> ").replace("\'","")+"\n"
            return Output
        
        N = self.N
        Output = GLOBAL.language["main_CMDisplayPathsIn"][0]+self.name+":\n\n"
        for i in range(0,N):
            for j in range(0,N):
                Output = Output + GLOBAL.language["main_CMDisplayPathsFrom"][0]+self.names[i]+GLOBAL.language["main_CMDisplayPathsTo"][0]+self.names[j]+":\n"+PathRep(self.Paths[i][j])+"\n"
        return Output


    ##########
    # FUNCTION: DisplayLoops
    def DisplayLoops(self):
        """Return the loops formatted for ascii display"""
        def IndexList(A, B):
            out = []
            for i in B:
                out = out+[A[i]]
            return out
            
        def LoopRep(Loops):
            Output = ""
            for index in range(0,len(Loops)):
                Output = Output+"\t"+str(IndexList(self.names,Loops[index]))[1:-1].replace(", "," -> ").replace("\'","")+"\n"
            return Output
        
        N = self.N
        Output = GLOBAL.language["main_CMDisplayLoopsIn"][0]+self.name+":\n"+LoopRep(self.Loops)+"\n"
        return Output


    ##########
    # FUNCTION: DisplayCEM
    def DisplayCEM(self):
        """Format the CEM for ascii text display; return a string"""

        def CEMRep(a_ij):
            """Format an element of the CEM data for ascii printing; return a string."""
            if a_ij == 1 or a_ij == "+":
                return "+"
            if a_ij == None or a_ij == "?":
                return "?"
            if a_ij == -1 or a_ij == "-":
                return "-"
            if a_ij == 0 or a_ij == "0":
                return "0"
        
        N = self.N
        
        # Set up the Spacers information and table width
        #    Spacers[0] are the variable names
        #    Spacers[1] are the lengths of the variable names
        #    Spacers[2] are the column 1 offsets for each variable
        #    Spacers[3] are the left-side offsets for each Adjoint element
        #    Spacers[4] are the right-side offsets for each Adjoint element
        MinSpace = 1
        Spacers = [copy(self.names),range(0,N), range(0,N), range(0,N), range(0,N)]
        Col1Width = self.LongestNameLen()
        TableWidth = Col1Width
        for i in range(0,N):
            Spacers[1][i] = len(Spacers[0][i])
            if Spacers[1][i] < MinSpace:
                Spacers[1][i] = MinSpace
            TableWidth = TableWidth + Spacers[1][i] + 1
            Spacers[2][i] = Col1Width - Spacers[1][i]
            Spacers[3][i] = Spacers[1][i]/2 + Spacers[1][i]%2 -1
            Spacers[4][i] = Spacers[1][i]/2
            
        if TableWidth < len(self.name)+Col1Width*len(self.names):
            TableWidth = len(self.name)+Col1Width*len(self.names)
        TableWidth = max(TableWidth,(len(self.name)),len(GLOBAL.language["main_CMPredictionMatrix"][0]))
        # Output will be written to Output
        Output = " "*TableWidth+"\n"
        
        # Create the title
        Output = Output+GLOBAL.language["main_CMPredictionMatrix"][0]+"\n"+str(self.name)+"\n\n"

        # Create the column headings
        Output = Output + " "*Col1Width
        for VarName in Spacers[0]:
            NewVarName = ""
            for index in range(0,len(VarName)):
                if VarName[index] != "\n":
                    NewVarName = NewVarName+VarName[index]
                else:
                    NewVarName = NewVarName+" "
            Output = Output + " " + NewVarName
        Output = Output + "\n"
        
        # Create row headings and populate rows
        for i in range(0,N):

            # translate line breaks into spaces
            NewVarName = ""
            for index in range(0,len(Spacers[0][i])):
                if Spacers[0][i][index] != "\n":
                    NewVarName = NewVarName+Spacers[0][i][index]
                else:
                    NewVarName = NewVarName+" "
            
            Output = Output + " "*Spacers[2][i] + NewVarName
            for j in range(0,N):
                Output = Output + " "+ " "*Spacers[3][j] + CEMRep(self.CEM[i][j]) + " "*Spacers[4][j]
            Output = Output + "\n"
        
        return Output


    ##########
    # FUNCTION: DisplayCorrelations
    def DisplayCorrelations(self):
        """Format correlation matrices for ascii display"""
        
        def CorrelationRep(a_ij):
            """Format an element of the Correlations data for ascii printing; return a string."""
            if a_ij == 1:
                return "+"
            if a_ij == None:
                return "?"
            if a_ij == -1:
                return "-"
            if a_ij == 0:
                return "0"
            if a_ij == 2:
                return " "
        
        N = len(self.CEM)
        
        # Set up the Spacers information and table width
        #    Spacers[0] are the variable names
        #    Spacers[1] are the lengths of the variable names
        #    Spacers[2] are the column 1 offsets for each variable
        #    Spacers[3] are the left-side offsets for each Adjoint element
        #    Spacers[4] are the right-side offsets for each Adjoint element
        MinSpace = 1
        Spacers = [copy(self.names),range(0,N), range(0,N), range(0,N), range(0,N)]
        Col1Width = self.LongestNameLen()
        TableWidth = Col1Width
        for i in range(0,N):
            Spacers[1][i] = len(Spacers[0][i])
            if Spacers[1][i] < MinSpace:
                Spacers[1][i] = MinSpace
            TableWidth = TableWidth + Spacers[1][i] + 1
            Spacers[2][i] = Col1Width - Spacers[1][i]
            Spacers[3][i] = Spacers[1][i]/2 + Spacers[1][i]%2 -1
            Spacers[4][i] = Spacers[1][i]/2
            
        if TableWidth < len(self.name)+Col1Width*len(self.names):
            TableWidth = len(self.name)+Col1Width*len(self.names)
        TableWidth = max(TableWidth,(len(self.name)),len("Prediction Matrix"))
        # Output will be written to Output
        Output = " "*TableWidth+"\n"
        
        # Create the title
        Output = Output+GLOBAL.language["main_CMCorrelationMatrices"][0]+str(self.name)+"\n\n"

        # Creat N correlation matrices, one for input at each variable
        for matrix in range(0,N):
            
            # Title the correlation matrix
            Output = Output + GLOBAL.language["main_CMCorrelationMatricesForInput"][0] + Spacers[0][matrix] + ":\n"
            # Create the column headings
            Output = Output + " "*Col1Width
            for VarName in Spacers[0]:
                NewVarName = ""
                for index in range(0,len(VarName)):
                    if VarName[index] != "\n":
                        NewVarName = NewVarName+VarName[index]
                    else:
                        NewVarName = NewVarName+" "
                Output = Output + " " + NewVarName
            Output = Output + "\n"
            
            # Create row headings and populate rows
            for i in range(0,N):

                # translate line breaks into spaces
                NewVarName = ""
                for index in range(0,len(Spacers[0][i])):
                    if Spacers[0][i][index] != "\n":
                        NewVarName = NewVarName+Spacers[0][i][index]
                    else:
                        NewVarName = NewVarName+" "
                
                Output = Output + " "*Spacers[2][i] + NewVarName
                for j in range(0,N):
                    Output = Output + " "+ " "*Spacers[3][j] + CorrelationRep(self.Correlations[matrix][i][j]) + " "*Spacers[4][j]
                Output = Output + "\n"
            Output = Output + "\n"
        return Output


    ##########
    # FUNCTION: DisplayAdjoint
    def DisplayAdjoint(self):
        """Format the Adjoint for ascii text display, return a string"""
        
        def LongestColLen(Adjoint):
            """Compute the length of the longest data column entry; return an integer."""
            N = len(Adjoint)
            length = range(0,N)
            for i in range(0,N):
                length[i] = 1
                for j in range(0,N):
                    if len(str(Adjoint[i][j])) > length[i]:
                        length[i] = len(str(Adjoint[i][j]))
            return length

        def ColWidth(c):
            """Compute the length of the longest column entry from either data or column name; return an integer."""
            N = len(self.Adjoint)
            width = 1
            for i in range(0, N):
                if self.Adjoint[i][c] != 0:
                    if width < len(str(self.Adjoint[i][c])):
                        width = len(str(self.Adjoint[i][c]))
            if len(self.names[c]) > width:
                width = len(self.names[c])
            return width

        N = len(self.Adjoint)
        
        # Set up the Spacers information and table width
        #    Spacers[0] are the variable names
        #    Spacers[1] are the lengths of the variable names
        #    Spacers[2] are the column 1 offsets for each variable
        #    Spacers[3] are the left-side offsets for each Adjoint element
        #    Spacers[4] are the right-side offsets for each Adjoint element
        #    Spacers[5] are the lengths of the longest

        MinSpace = 1
        Spacers = [copy(self.names),range(0,N), range(0,N), range(0,N), range(0,N), LongestColLen(self.Adjoint)]
        Col1Width = self.LongestNameLen()
        TableWidth = Col1Width
        for i in range(0,N):
            Spacers[1][i] = len(Spacers[0][i])
            if Spacers[1][i] < MinSpace:
                Spacers[1][i] = MinSpace
            TableWidth = TableWidth + Spacers[1][i] + 1
            Spacers[2][i] = Col1Width - Spacers[1][i]
            Spacers[4][i] = 0
            Spacers[3][i] = 0
            
        if TableWidth < len(self.name)+Col1Width*len(self.names):
            TableWidth = len(self.name)+Col1Width*len(self.names)
        TableWidth = max(TableWidth,(len(self.name)),len(GLOBAL.language["main_CMAdjointMatrix"][0]))
        # Output will be written to Output
        Output = " "*TableWidth+"\n"
        
        # Create the title
        Output = Output + GLOBAL.language["main_CMAdjointMatrix"][0]+"\n" + self.name + "\n\n"

        # Create the column headings
        Output = Output + " "*Col1Width
        count = -1
        for VarName in Spacers[0]:
            count = count + 1
            NewVarName = ""
            for index in range(0,len(VarName)):
                if VarName[index] != "\n":
                    NewVarName = NewVarName+VarName[index]
                else:
                    NewVarName = NewVarName+" "
            Output = Output + " "*(ColWidth(count)+1-len(VarName)) + NewVarName
        Output = Output + "\n"
        
        # Create row headings and populate rows
        for i in range(0,N):

            # translate line breaks into spaces
            NewVarName = ""
            for index in range(0,len(Spacers[0][i])):
                if Spacers[0][i][index] != "\n":
                    NewVarName = NewVarName+Spacers[0][i][index]
                else:
                    NewVarName = NewVarName+" "
            
            Output = Output + " "*Spacers[2][i] + NewVarName
            for j in range(0,N):
                Output = Output +" " + " "*(ColWidth(j) - len(str(self.Adjoint[i][j]))) + str(self.Adjoint[i][j])
            Output = Output + "\n"
        
        return Output

    ##########
    # FUNCTION: DisplayT
    def DisplayT(self):
        """Format the T matrix for ascii text display, return a string"""
        def LongestColLen(T):
            """Compute the length of the longest data column entry; return an integer."""
            N = self.N
            length = range(0,N)
            for i in range(0,N):
                length[i] = 1
                for j in range(0,N):
                    if len(str(T[i][j])) > length[i]:
                        length[i] = len(str(T[i][j]))
            return length

        def ColWidth(c):
            """Compute the length of the longest column entry from either data or column name; return an integer."""
            N = self.N
            width = 1
            for i in range(0, N):
                if self.T[i][c] != 0:
                    if width < len(str(self.T[i][c])):
                        width = len(str(self.T[i][c]))
            if len(self.names[c]) > width:
                width = len(self.names[c])
            return width

        N = self.N
        
        # Set up the Spacers information and table width
        #    Spacers[0] are the variable names
        #    Spacers[1] are the lengths of the variable names
        #    Spacers[2] are the column 1 offsets for each variable
        #    Spacers[3] are the left-side offsets for each Adjoint element
        #    Spacers[4] are the right-side offsets for each Adjoint element
        #    Spacers[5] are the lengths of the longest

        MinSpace = 1
        Spacers = [copy(self.names),range(0,N), range(0,N), range(0,N), range(0,N), LongestColLen(self.T)]
        Col1Width = self.LongestNameLen()
        TableWidth = Col1Width
        for i in range(0,N):
            Spacers[1][i] = len(Spacers[0][i])
            if Spacers[1][i] < MinSpace:
                Spacers[1][i] = MinSpace
            TableWidth = TableWidth + Spacers[1][i] + 1
            Spacers[2][i] = Col1Width - Spacers[1][i]
            Spacers[4][i] = 0
            Spacers[3][i] = 0
            
        if TableWidth < len(self.name)+Col1Width*len(self.names):
            TableWidth = len(self.name)+Col1Width*len(self.names)
        TableWidth = max(TableWidth,(len(self.name)),len(GLOBAL.language["main_CMTotalFeedback"][0]))
        # Output will be written to Output
        Output = " "*TableWidth+"\n"
        
        # Create the title
        Output = Output + GLOBAL.language["main_CMTotalFeedback"][0]+"\n" + self.name + "\n\n"

        # Create the column headings
        Output = Output + " "*Col1Width
        count = -1
        for VarName in Spacers[0]:
            count = count + 1
            NewVarName = ""
            for index in range(0,len(VarName)):
                if VarName[index] != "\n":
                    NewVarName = NewVarName+VarName[index]
                else:
                    NewVarName = NewVarName+" "
            Output = Output + " "*(ColWidth(count)+1-len(VarName)) + NewVarName
        Output = Output + "\n"
        
        # Create row headings and populate rows
        for i in range(0,N):

            # translate line breaks into spaces
            NewVarName = ""
            for index in range(0,len(Spacers[0][i])):
                if Spacers[0][i][index] != "\n":
                    NewVarName = NewVarName+Spacers[0][i][index]
                else:
                    NewVarName = NewVarName+" "
            
            Output = Output + " "*Spacers[2][i] + NewVarName
            for j in range(0,N):
                Output = Output +" " + " "*(ColWidth(j) - len(str(self.T[i][j]))) + str(self.T[i][j])
            Output = Output + "\n"
        
        return Output


    ##########
    # FUNCTION: DisplayWFM
    def DisplayWFM(self):
        """Format the WFM for ascii text display; return a string"""
        def LongestColLen():
            return 2+GLOBAL.WeightedFeedbackPrecision

        def ColWidth(c):
            N = len(self.WFM)
            width = 2+GLOBAL.WeightedFeedbackPrecision
            if len(self.names[c]) > width:
                width = len(self.names[c])
            return width

        N = len(self.Adjoint)
        
        # Set up the Spacers information and table width
        #    Spacers[0] are the variable names
        #    Spacers[1] are the lengths of the variable names
        #    Spacers[2] are the column 1 offsets for each variable
        #    Spacers[3] are the left-side offsets for each Adjoint element
        #    Spacers[4] are the right-side offsets for each Adjoint element
        #    Spacers[5] are the lengths of the longest

        MinSpace = 1
        Spacers = [copy(self.names),range(0,N), range(0,N), range(0,N), range(0,N), LongestColLen()]
        Col1Width = self.LongestNameLen()
        TableWidth = Col1Width
        for i in range(0,N):
            Spacers[1][i] = len(Spacers[0][i])
            if Spacers[1][i] < MinSpace:
                Spacers[1][i] = MinSpace
            TableWidth = TableWidth + Spacers[1][i] + 1
            Spacers[2][i] = Col1Width - Spacers[1][i]
            Spacers[4][i] = 0
            Spacers[3][i] = 0
            
        if TableWidth < len(self.name)+((GLOBAL.WeightedFeedbackPrecision-1)+Col1Width)*len(self.names):
            TableWidth = len(self.name)+((GLOBAL.WeightedFeedbackPrecision-1)+Col1Width)*len(self.names)
        TableWidth = max(TableWidth+(GLOBAL.WeightedFeedbackPrecision+2)*N,(len(self.name)),len(GLOBAL.language["main_CMWeightedFeedbackMatrix"][0]))
        # Output will be written to Output
        Output = " "*TableWidth+"\n"
        
        # Create the title
        Output = Output + GLOBAL.language["main_CMWeightedFeedbackMatrix"][0]+"\n" + self.name + "\n\n"

        # Create the column headings
        Output = Output + " " + " "*(Col1Width - 1)
        count = -1
        for VarName in Spacers[0]:
            count = count + 1
            NewVarName = ""
            for index in range(0,len(VarName)):
                if VarName[index] != "\n":
                    NewVarName = NewVarName+VarName[index]
                else:
                    NewVarName = NewVarName+" "
            Output = Output + " "*(GLOBAL.WeightedFeedbackPrecision - 1) + " "*(ColWidth(count)+1-len(VarName)) + NewVarName
        Output = Output + "\n"
        
        # Create row headings and populate rows
        for i in range(0,N):

            # translate line breaks into spaces
            NewVarName = ""
            for index in range(0,len(Spacers[0][i])):
                if Spacers[0][i][index] != "\n":
                    NewVarName = NewVarName+Spacers[0][i][index]
                else:
                    NewVarName = NewVarName+" "
            
            Output = Output + " "*Spacers[2][i] + NewVarName
            for j in range(0,N):
                Output = Output +" " + " "*(ColWidth(j) - 3) + str(self.WFM[i][j])
            Output = Output + "\n"
        
        return Output


    ##########
    # FUNCTION: DisplayWPM
    # DisplayWPM formats the weighted prediction matrix
    def DisplayWPM(self):
        
        def LongestColLen():
            return 3

        def ColWidth(c):
            N = len(self.WPM)
            width = 3
            if len(self.names[c]) > width:
                width = len(self.names[c])
            return width

        def WPMRep(a_ij):
            if a_ij == 1 or a_ij == "+":
                return " + "
            if a_ij == None or a_ij == "?":
                return " ? "
            if a_ij == -1 or a_ij == "-":
                return " - "
            if a_ij == 0 or a_ij == "0":
                return " 0 "
            if a_ij == 2:
                return "(+)"
            if a_ij == -2:
                return "(-)"

        N = len(self.WPM)
        
        # Set up the Spacers information and table width
        #    Spacers[0] are the variable names
        #    Spacers[1] are the lengths of the variable names
        #    Spacers[2] are the column 1 offsets for each variable
        #    Spacers[3] are the left-side offsets for each Adjoint element
        #    Spacers[4] are the right-side offsets for each Adjoint element
        #    Spacers[5] are the lengths of the longest

        MinSpace = 1
        Spacers = [copy(self.names),range(0,N), range(0,N), range(0,N), range(0,N), LongestColLen()]
        Col1Width = self.LongestNameLen()
        TableWidth = Col1Width
        for i in range(0,N):
            Spacers[1][i] = len(Spacers[0][i])
            if Spacers[1][i] < MinSpace:
                Spacers[1][i] = MinSpace
            TableWidth = TableWidth + Spacers[1][i] + 1
            Spacers[2][i] = Col1Width - Spacers[1][i]
            Spacers[4][i] = 0
            Spacers[3][i] = 0
            
        # Create the title, and update TableWidth
        CriterionString = ">= "
        if GLOBAL.ThresholdCriterion == 0:
            CriterionString = "> "
        TableWidth = max(len(self.name)+Col1Width*len(self.names), len(GLOBAL.language["main_CMWFMPredictions"][0]+CriterionString+str(GLOBAL.WeightedPredictionThreshold)), TableWidth)
        TableWidth = max(TableWidth,(len(self.name)),len(GLOBAL.language["main_CMWFMPredictionMatrix"][0]),len(GLOBAL.language["main_CMWFMPredictions"][0]))
        
        # Output will be written to Output
        Output = " "*TableWidth+"\n"
        Output = Output + GLOBAL.language["main_CMWFMPredictionMatrix"][0] + "\n"+self.name + "\n\n"+GLOBAL.language["main_CMWFMPredictions"][0]+CriterionString+str(GLOBAL.WeightedPredictionThreshold)+"\n\n"

        # Create the column headings
        Output = Output + " " + " "*(Col1Width - 1)
        count = -1
        for VarName in Spacers[0]:
            count = count + 1
            NewVarName = ""
            for index in range(0,len(VarName)):
                if VarName[index] != "\n":
                    NewVarName = NewVarName+VarName[index]
                else:
                    NewVarName = NewVarName+" "
            if len(VarName) > 1:
                Output = Output + " "*(ColWidth(count)+1-len(VarName)) + NewVarName
            else:
                Output = Output + " "*(ColWidth(count)-len(VarName)) + NewVarName + " "
        Output = Output + "\n"
        
        # Create row headings and populate rows
        for i in range(0,N):

            # translate line breaks into spaces
            NewVarName = ""
            for index in range(0,len(Spacers[0][i])):
                if Spacers[0][i][index] != "\n":
                    NewVarName = NewVarName+Spacers[0][i][index]
                else:
                    NewVarName = NewVarName+" "
            
            Output = Output + " "*Spacers[2][i] + NewVarName
            for j in range(0,N):
                Output = Output +" " + " "*(ColWidth(j) - 3) + WPMRep(self.WPM[i][j])
            Output = Output + "\n"
        
        return Output


    ##########
    # FUNCTION: DisplayCLEM
    # DisplayCLEM formats the change in life expectancy matrix as ascii text
    def DisplayCLEM(self):
        def LongestColLen(Adjoint):
            N = len(Adjoint)
            length = range(0,N)
            for i in range(0,N):
                length[i] = 1
                for j in range(0,N):
                    if len(str(Adjoint[i][j])) > length[i]:
                        length[i] = len(str(Adjoint[i][j]))
            return length

        def ColWidth(c):
            N = len(self.Adjoint)
            width = 3
            if len(self.names[c]) > width:
                width = len(self.names[c])
            return width

        def CLEMRep(a_ij):
            if a_ij == 1 or a_ij == "+":
                return "+"
            if a_ij == None or a_ij == "?":
                return "?"
            if a_ij == -1 or a_ij == "-":
                return "-"
            if a_ij == 0 or a_ij == "0":
                return "0"

        N = len(self.Adjoint)
        
        # Set up the Spacers information and table width
        #    Spacers[0] are the variable names
        #    Spacers[1] are the lengths of the variable names
        #    Spacers[2] are the column 1 offsets for each variable
        #    Spacers[3] are the left-side offsets for each Adjoint element
        #    Spacers[4] are the right-side offsets for each Adjoint element
        #    Spacers[5] are the lengths of the longest

        MinSpace = 1
        Spacers = [copy(self.names),range(0,N), range(0,N), range(0,N), range(0,N), LongestColLen(self.Adjoint)]
        Col1Width = self.LongestNameLen()
        TableWidth = Col1Width
        for i in range(0,N):
            Spacers[1][i] = len(Spacers[0][i])
            if Spacers[1][i] < MinSpace:
                Spacers[1][i] = MinSpace
            TableWidth = TableWidth + Spacers[1][i] + 1
            Spacers[2][i] = Col1Width - Spacers[1][i]
            Spacers[4][i] = 0
            Spacers[3][i] = 0
            
        if TableWidth < len(self.name)+Col1Width*len(self.names):
            TableWidth = len(self.name)+Col1Width*len(self.names)
        TableWidth = max(TableWidth,(len(self.name))    ,len(GLOBAL.language["main_CMChangeInLEMatrix"][0]))
        # Output will be written to Output
        Output = " "*TableWidth+"\n"
        
        # Create the title
        Output = Output + GLOBAL.language["main_CMChangeInLEMatrix"][0]+"\n" + self.name + "\n\n"

        # Create the column headings
        Output = Output + " " + " "*(Col1Width - 1)
        count = -1
        for VarName in Spacers[0]:
            count = count + 1
            NewVarName = ""
            for index in range(0,len(VarName)):
                if VarName[index] != "\n":
                    NewVarName = NewVarName+VarName[index]
                else:
                    NewVarName = NewVarName+" "
            if len(VarName) > 1:
                Output = Output + " "*(ColWidth(count)+1-len(VarName)) + NewVarName
            else:
                Output = Output + " "*(ColWidth(count)-len(VarName)) + NewVarName + " "
        Output = Output + "\n"
        
        # Create row headings and populate rows
        for i in range(0,N):

            # translate line breaks into spaces
            NewVarName = ""
            for index in range(0,len(Spacers[0][i])):
                if Spacers[0][i][index] != "\n":
                    NewVarName = NewVarName+Spacers[0][i][index]
                else:
                    NewVarName = NewVarName+" "
            
            Output = Output + " "*Spacers[2][i] + NewVarName
            for j in range(0,N):
                if i != j:
                    Output = Output +" " + " "*(ColWidth(j) - 3) + " " + CLEMRep(self.CLEM[i][j]) + " "
                else:
                    Output = Output +" " + " "*(ColWidth(j) - 3) + CLEMRep(self.CLEM[i][j][0]) + "," + CLEMRep(self.CLEM[i][j][1]) 
            Output = Output + "\n"
        
        return Output

    pass

##########
# Class for library of CommunityMatrices CMLibrary.py
class CMLibrary:
    def __init__(self, Name = GLOBAL.language["main_CMLibraryName"][0], Version = "1.2", PrefsGraph = True, PrefsCEM = True, PrefsAdjoint = True, PrefsT = True, PrefsWFM = True, PrefsWPM = True, PrefsCLEM = True, PrefsConfirmOnDelete = True, PrefsConfirmOnSave = True, PrefsConfirmOnClearLibrary = True, CommunityMatrices = []):
        """Construct a CMLibrary object and initialize its variables; return a CMLibrary instance."""
        # validate the suppied objects as community matrices
        for x in CommunityMatrices:
            if not isinstance(x, CommunityMatrix):
                print "\'"+str(x)+"\'"+GLOBAL.language["main_CMLibraryNotCMAlert"][0]
                return
        # set up the variables
        self.Name = Name
        self.Version = Version
        self.PrefsGraph = PrefsGraph
        self.PrefsCEM = PrefsCEM
        self.PrefsAdjoint = PrefsAdjoint
        self.PrefsT = PrefsT
        self.PrefsWFM = PrefsWFM
        self.PrefsWPM = PrefsWPM
        self.PrefsCLEM = PrefsCLEM
        self.PrefsConfirmOnDelete = PrefsConfirmOnDelete
        self.PrefsConfirmOnSave = PrefsConfirmOnSave
        self.PrefsConfirmOnClearLibrary = PrefsConfirmOnClearLibrary
        self.CommunityMatrices = CommunityMatrices[:]
        self.RecentFiles = []
        self.MakeNames()
        return
        
    def __repr__(self):
        """Format the CMLibrary input for ascii representation; return a string."""
        OUTPUT = "["+self.Name+", "+self.Version+", "+str(self.PrefsGraph)+", "+str(self.PrefsCEM)+", "+str(self.PrefsAdjoint)+", "+str(self.PrefsT)+", "+str(self.PrefsWFM)+", "+str(self.PrefsWPM)+", "+str(self.PrefsCLEM)+", "+str(self.names)+"]"
        return OUTPUT
        
    def AddCM(self,NAME):
        """Add a single CommunityMatrix object to the CMLibrary; modifies a CMLibrary instance."""
        # Confirm that the supplied object is a CommunityMatrix
        if not isinstance(NAME, CommunityMatrix):
            print "\'"+str(NAME)+"\'"+GLOBAL.language["main_CMLibraryNotCMAlert"][0]
            return
        
        # Reset the matrix' flags .  .  .
        NAME.GraphFlag = False
        NAME.CEMFlag = False
        NAME.PathsFlag = False
        NAME.AdjointFlag = False
        NAME.WFMFlag = False
        NAME.WPMFlag = False
        NAME.CLEMFlag = False        
        
        # Confirm that the name of the CM is not already taken
        Alternate = deepcopy(NAME)
        Count = 2
        index = 0
        for x in self.names:
            if x == Alternate.name:
                index = index + 1
                break
        for x in self.names:
            if Alternate.name == x:
                while Alternate.name+str(Count) in self.names:
                    Count = Count + 1
                Alternate.name = Alternate.name+str(Count)
        
        # Add the supplied CommunityMatrix to the CMLibrary object
        self.CommunityMatrices = self.CommunityMatrices+[Alternate]
        self.MakeNames()
        return
        # end AddCM()
    
    def MakeNames(self):
        """Return a list of strings containing the names of the CommunityMatrix objetcs in a CM Library"""
        self.names = []
        for x in self.CommunityMatrices:
            self.names = self.names+[x.name]
        
    def ProcessVariableName(self, Name):
        """Translate line break characters "\n" in a string to render literally: "\\n"; return a string."""
        NewName = ""
        for index in range(0,len(Name)):
            if Name[index] != "\n":
                NewName = NewName+Name[index]
            else:
                NewName = NewName+"\\n"
        return NewName

    def LengthVariableName(self, Name):
        """Compute the length of the longest line of a possibly multi-line string; return an integer."""
        lines = Name.split("\n")
        Length = 1
        for i in lines:
            Length = max(len(i),Length)
        return Length

    def MakeGraph(self):
        """Make a CommunityMatrix object's graph in dot representation and in bitmap representation and stores them in Graph and Graphed"""
        # if the ListBox is not empty...
        if len(self.CommunityMatrices) > 0:
            if frame.ListBox.GetCount() > 0:
                index = deepcopy(int(frame.ListBox.GetSelection()))
            else:
                index = 0
            CM = GLOBAL.Library.CommunityMatrices[index]
                
            # Deal with greyscale if necessary
            if GLOBAL.GraphColoring == 1:
                Greyscale = CM.N*[""]
                for i in range(0,CM.N):
                    chunk = i*(255.0/(CM.N + 3))
                    if chunk > 15:
                        chunk = str(hex(int(chunk))[-2:])
                    else:
                        chunk = "0"+str(hex(int(chunk))[-1])
                    chunk = "#"+chunk*3
                    Greyscale[i] = chunk

            # Define arrowhead style
            if GLOBAL.GraphColoring == 0:
                arrowhead = "odot"
            if GLOBAL.GraphColoring > 0:
                arrowhead = "dot"

            # Determine the maximum string length of any variable name
            max_name_len = 1
            for j in range(0,len(CM.names)):
                if self.LengthVariableName(str(CM.names[j])) > max_name_len:
                    max_name_len = self.LengthVariableName(str(CM.names[j]))
            
            if ( (hasattr(CM, "GraphFlag") == False) or (GLOBAL.Library.PrefsGraph == True and CM.GraphFlag == False) ):
                if hasattr(CM, "GraphFlag") == False:
                    GLOBAL.Library.PrefsGraph = True
                N = CM.N
                GRAPH = "digraph G {\ngraph [bgcolor = \"transparent\", size = \"18!,18!\", nodesep=\"1\", ranksep=\"1\", rankdir=\"LR\"];\nnode [fixedsize=true, fontname=\"Sans\", fontsize=\""+str((58/max_name_len)+(12-1.05**max_name_len))+"\", shape=circle, height=\"2\", width=\"2\", style=\"setlinewidth(5)\"];\nedge [style=\"setlinewidth(4)\", arrowsize=3];\n"
                for j in range(0,N):
                    jName = self.ProcessVariableName(str(CM.names[j]))
                    if GLOBAL.GraphColoring == 0:
                        GRAPH=GRAPH+"\t\""+jName+"\" [color=\"#000000\"];\n"
                    if GLOBAL.GraphColoring == 1:
                        GRAPH=GRAPH+"\t\""+jName+"\" [color=\""+str(Greyscale[j])+"\"];\n"
                    if GLOBAL.GraphColoring == 2:
                        GRAPH=GRAPH+"\t\""+jName+"\" [color=\""+str(GLOBAL.CM_Colors[j])+"\"];\n"
                    for i in range(0,N):
                        iName = self.ProcessVariableName(str(CM.names[i]))
                        if (CM.A[i,j] != 0):
                            GRAPH = GRAPH+"\t\t\""+(jName+"\" -> \""+iName)+"\""
                            if GLOBAL.GraphColoring == 0:
                                GRAPH = GRAPH+" [color=\"#000000\""
                            if GLOBAL.GraphColoring == 1:
                                GRAPH = GRAPH+" [color=\""+str(Greyscale[j])+"\""
                            if GLOBAL.GraphColoring == 2:
                                GRAPH = GRAPH+" [color=\""+str(GLOBAL.CM_Colors[j])+"\""
                            if (CM.A[i,j] == -1):
                                GRAPH = GRAPH+", arrowhead="+arrowhead
                            GRAPH = GRAPH+"];\n"
                GRAPH = GRAPH+"}"
                CM.Graph = deepcopy(GRAPH)

                # temporarily write out the graph in dot format, and the image in png format
                dotpath = str(gettempdir())+"/tmp.dot"
                pngpath = str(gettempdir())+"/tmp.png"
                dotfile = open(dotpath,'w+b')
                dotfile.writelines(GRAPH)
                dotfile.close()

                args = " -Tpng "+dotpath+" > "+pngpath
#		print "before if \n"
		# WORKAROUND GLOBAL.dotLocation wasn't set so I set it here, to verify - oli
		GLOBAL.dotLocation = "/usr/bin/dot"
                if GLOBAL.dotLocation != "":
#		    print "after if \n"
                    status = system(GLOBAL.dotLocation + args)
#		    print status
#		    print "\n \n"
                    pngfile = open(pngpath,'rb')
                    CM.Graphed = pngfile.read()
                    pngfile.close()
                    remove(dotpath)
                    remove(pngpath)
                    CM.GraphFlag = True
                else:
                    CM.GraphFlag = False
            else:
                if GLOBAL.Library.PrefsGraph == False:
                    CM.Graph = GLOBAL.language["main_CMLibraryMakeGraphNone"][0]

    def DeleteCM(self,NAME):
        """Delete the first CommunityMatrix object with name NAME from the CMLibrary"""
        for x in range(0,len(self.CommunityMatrices)):
            if NAME == self.CommunityMatrices[x].name:
                del self.CommunityMatrices[x]
                self.MakeNames()
                break
                
    def Transpose(self, M):
        """Return transpose of M"""
        N = len(M)
        T = [range(0,N)]
        for i in range(0,N-1):
            T = T + [range(0,N)]
        for i in range(0,N):
            for j in range(0,N):
                T[i][j] = M[j][i]
        return T
    
    def SquareMatrix(self, N):
        """Return a square matrix"""
        Matrix = [range(0,N)]
        for i in range(0,N-1):
            Matrix = Matrix + [range(0,N)]
        for i in range(0,N):
            for j in range(0,N):
                Matrix[i][j] = 0
        return Matrix

    def IsLoop(self):
        """Test that a list of visited elements begins at and terminates in the jth parameterl returns boolean"""
        if ((GLOBAL.LLOVE[-1] == GLOBAL.LLOVE[0]) and (len(GLOBAL.LLOVE) > 1)):
            return True
        else:
            return False

    def LoopMakeENVY(self):
        """Compute from GLOBAL.CCM, GLOBAL.LLOVE, and GLOBAL.LTerm which Elements are Not Visited Yet, excluding the first element of the loop; returns a list"""
        ENVY = None
        N = len(GLOBAL.CCM)
        for z in range(GLOBAL.x,N):
            if GLOBAL.CCM[z][GLOBAL.LLOVE[-1]] != 0:
                if GLOBAL.LTerm[GLOBAL.LLOVE[-1]][z] == 0:
                    if ENVY == None:
                        ENVY = [z]
                    else:
                        ENVY = ENVY+[z]
        if ENVY != None:
            for z in GLOBAL.LLOVE[1:]:
                ENVY = [x for x in ENVY if x != z]
        if ENVY == []:
            ENVY = None
        return ENVY

    def LoopUpdateTerm(self):
        """Set to zero all terms in the rows in GLOBAL.Term corresponding to elements not in GLOBAL.LOVE."""
        N = len(GLOBAL.CCM)
        for y in range(0,N):
            if y not in GLOBAL.LLOVE:
                for z in range(0,N):
                    GLOBAL.LTerm[y][z] = 0

        for xx in range(0,(GLOBAL.x-1)):
            for q in range(0,N):
                GLOBAL.LTerm[xx][q] = 1
                GLOBAL.LTerm[q][xx] = 1

    def AddLOVEtoLOL(self):
        """Add GLOBAL.LOVE to GLOBAL.LOL"""
        if GLOBAL.LOL == []:
            GLOBAL.LOL = [GLOBAL.LLOVE]
        else:
            GLOBAL.LOL = GLOBAL.LOL+[GLOBAL.LLOVE]

    def LoopSearchStep(self):
        """Compute and compile a List of Loops given GLOBAL.LLOVE and GLOBAL.LTerm; modify GLOBAL.LOL"""
        ENVY = GLOBAL.Library.LoopMakeENVY()
        if ENVY == None:
            if len(GLOBAL.LLOVE) > 1:
                GLOBAL.LTerm[GLOBAL.LLOVE[-2]][GLOBAL.LLOVE[-1]] = 1
            GLOBAL.LLOVE = GLOBAL.LLOVE[:-1]
            GLOBAL.Library.LoopUpdateTerm()

            # exit SearchStep if the last element of GLOBAL.LOVE is i or if GLOBAL.LOVE is empty 
            # and return List Of Loops (GLOBAL.LOL)
            if len(GLOBAL.LLOVE) == 0:
                GLOBAL.incomplete = False
                return
        else:
            # append the first element (breadthwise search) of ENVY to GLOBAL.LOVE
            GLOBAL.LLOVE = GLOBAL.LLOVE+[ENVY[0]]

            # test whether new GLOBAL.LOVE is a loop and respond accordingly
            if GLOBAL.Library.IsLoop():
                GLOBAL.Library.AddLOVEtoLOL()
                GLOBAL.LTerm[GLOBAL.LLOVE[-2]][GLOBAL.LLOVE[-1]] = 1
                GLOBAL.LLOVE = GLOBAL.LLOVE[:-1]

    def printLOL():
        """Prints GLOBAL.LOL in human readable form to stout."""
        for m in range(0,len(GLOBAL.LOL)):
            temp = GLOBAL.LOL[m]
            for n in range(0,len(temp)):
                temp[n] = temp[n]
            print "GLOBAL.LOL: "+str(temp)

    def printMOSL():
        """Prints GLOBAL.MOSL in human readable form to stout."""
        r = len(GLOBAL.MOSL)
        for i in range(0,r):
            for j in range(0,r):
                if i+j < r:
                    depth = len(GLOBAL.MOSL[i][j])
                    for k in range(0,depth):
                        if k == 0:
                            print "\nMOSL["+str(i)+"]["+str(j)+"]:  ",
                        if k > 0:
                            print GLOBAL.MOSL[i][j][k],
                            if k < depth:
                                print ", ",
        print "\n"

    def printLTerm():
        """Prints GLOBAL.LTerm in human readable form to stout."""
        r = len(GLOBAL.LTerm)
        for i in range(0,r):
            for j in range(0,r):
                if i+j < r:
                    depth = len(GLOBAL.LTerm[i][j])
                    for k in range(0,depth):
                        if k == 0:
                            print "\nTerm["+str(i)+"]["+str(j)+"]:  ",
                        if k > 0:
                            print GLOBAL.LTerm[i][j][k],
                            if k < depth:
                                print ", ",
        print "\n"

    def printSOSL(SOSL):
        """Prints GLOBAL.SOSL in human readable form to stout."""
        rows = len(SOSL)
        print "SOSL:"
        for i in range(0,rows):
            print "  ",
            depth = len(SOSL[i])
            for m in range(0,depth):
                print str(SOSL[i][m]),
            print
        print

    def EnumerateLoops(self, CM):
        """Enumerate a list of loops (simple cycles) in CM; modify GLOBAL.LOL and return a list."""
        GLOBAL.CCM = deepcopy(CM)

        # Set N = rowsize of CM
        N = len(GLOBAL.CCM)

        # initialize search termination matrix
        GLOBAL.LTerm = GLOBAL.Library.SquareMatrix(N)

        # initialize list of loops (GLOBAL.LOL), and list of visited elements (GLOBAL.LLOVE)
        GLOBAL.LOL = []

        for x in range(0,N-1):
            GLOBAL.x = x
            GLOBAL.LLOVE = [x]
            for xx in range(0,x):
                for q in range(0,N):
                    GLOBAL.LTerm[xx][q] = 1
                    GLOBAL.LTerm[q][xx] = 1

            # find all loops starting at x
            GLOBAL.incomplete = True
            while GLOBAL.incomplete:
                GLOBAL.Library.LoopSearchStep()

        if GLOBAL.CCM[N-1][N-1] != 0:
            GLOBAL.LOL = GLOBAL.LOL+[[N-1,N-1]]

        return GLOBAL.LOL

    def MakeLoops(CM):
        """Enumerate the loops for the entire system; modifies CM.Loops"""
        if frame.ListBox.GetCount() > 0:
            index = deepcopy(int(frame.ListBox.GetSelection()))
            CM = GLOBAL.Library.CommunityMatrices[index]
            if ( (hasattr(CM, "LoopsFlag") == False) or (GLOBAL.Library.PrefsCEM == True and CM.LoopsFlag == False) ):
                if hasattr(CM, "LoopsFlag") == False:
                    GLOBAL.Library.PrefsCEM = True
                CM.Loops = GLOBAL.Library.EnumerateLoops(CM.A)
                CM.LoopsFlag = True

    def IsPath(self, j):
        """Test that GLOBAL.LOVE terminates in the jth variable; return a boolean."""
        if GLOBAL.LOVE[-1] == j:
            return True
        else:
            return False

    def MakeENVY(self, CM):
        """Compute from GLOBAL.CCM, GLOBAL.LOVE, and GLOBAL.Term which Elements are Not Visited Yet, excluding the first element of the path; returns a list"""
        ENVY = []
        for x in range(0,GLOBAL.N):
            if CM[x][GLOBAL.LOVE[-1]] != 0:
                if GLOBAL.Term[x][GLOBAL.LOVE[-1]] == 0:
                    ENVY = ENVY+[x]
        ENVY = [element for element in ENVY if element not in GLOBAL.LOVE]
        return ENVY

    def UpdateTerm(self):
        """Clear rows in GLOBAL.Term of any elements not in GLOBAL.LOVE; modify GLOBAL.Term"""
        N = GLOBAL.N
        for x in range(0,N):
            if x not in GLOBAL.LOVE:
                for y in range(0,N):
                    GLOBAL.Term[y][x] = 0

    def AddLOVEtoLOP(self):
        """Add GLOBAL.LOVE to GLOBAL.LOP"""
        if GLOBAL.LOP == []:
            GLOBAL.LOP = [GLOBAL.LOVE]
        else:
            GLOBAL.LOP = GLOBAL.LOP+[GLOBAL.LOVE]

    def SearchStep(self, CM, i, j):
        """Compute and compile a List of Paths paths to j in A; modify GLOBAL.LOP"""
        N = GLOBAL.N
        ENVY = GLOBAL.Library.MakeENVY(CM)
        # when there are no unvisited elements & GLOBAL.LOVE has more than 1 element, 
        # terminate the last element of GLOBAL.LOVE for the second to last element of 
        # GLOBAL.LOVE.
        if len(ENVY) == 0:
            if len(GLOBAL.LOVE) == 1:
                GLOBAL.Term[GLOBAL.LOVE[-1]][GLOBAL.LOVE[-1]] = 1
            if len(GLOBAL.LOVE) > 1:
                GLOBAL.Term[GLOBAL.LOVE[-1]][GLOBAL.LOVE[-2]] = 1
            GLOBAL.LOVE = GLOBAL.LOVE[:-1]
            GLOBAL.Library.UpdateTerm()

            # exit SearchStep if the last element of GLOBAL.LOVE is i & i is terminated
            # or if GLOBAL.LOVE is empty and return List Of Paths (GLOBAL.LOP)
            if len(GLOBAL.LOVE) == 0:
                GLOBAL.incomplete = False
            if len(GLOBAL.LOVE) == 1:
                test = False
                for val in [x for x in range(0,N) if x != i]:
                    if GLOBAL.Term[val][i] == 1:
                        test = True
                if test:
                    return
                
                for x in range(0,N):
                    GLOBAL.Term[x][GLOBAL.LOVE[-1]] = 1
                GLOBAL.LOVE = GLOBAL.LOVE[:-1]
                GLOBAL.Library.UpdateTerm()
                GLOBAL.incomplete = False

        else:
            # append the first element (breadthwise search) of ENVY to GLOBAL.LOVE
            GLOBAL.LOVE = GLOBAL.LOVE+[ENVY[0]]
            # test whether new GLOBAL.LOVE is a path from i to j and respond accordingly
            if GLOBAL.Library.IsPath(j):
                GLOBAL.Library.AddLOVEtoLOP()
                GLOBAL.Term[GLOBAL.LOVE[-1]][GLOBAL.LOVE[-2]] = 1
                GLOBAL.LOVE = GLOBAL.LOVE[:-1]

    def EnumeratePaths(self, CM, I, J):
        """Enumerate a list of paths from I to J, given CM; return s GLOBAL.LOP"""
        # Set N = rowsize of CM
        N = GLOBAL.N

        # take care of the simple case of i = j
        if I == J:
            return [[I,J]]

        # initialize search termination matrix
        GLOBAL.Term = GLOBAL.Library.SquareMatrix(N)

        # initialize list of paths (GLOBAL.LOP), list of visited elements (GLOBAL.LOVE)
        GLOBAL.LOP = []
        GLOBAL.LOVE = [I]

        GLOBAL.incomplete = True
        while GLOBAL.incomplete:
            GLOBAL.Library.SearchStep(CM,I,J)

        return GLOBAL.LOP

    def SetDiff(self, x, y):
        """Comput elements of x that are not in y; return a list."""
        Diff = []
        for i in x:
            if i not in y:
                Diff = Diff + [i]
        return Diff

    def PathCompliment(self, Path,N):
        """Compute the variables of the complimentary subsystem to Path; return a list."""
        return GLOBAL.Library.SetDiff(range(0,N),Path)

    def Unique(self, integers):
        """Compute unique values in a list of integers; return a list"""
        if len(integers) == 0:
            return []
        elements = {}
        for x in integers:
            elements[x] = 1
        return elements.keys()
    
    def IsElement(self, A, B):
        """Test whether any elements of list A are in list B; return a list."""
        if A == [None] or B == None:
            return [False]
        lenA = len(A)
        if lenA == 0 or len(B) == 0:
            return [False]
        out = range(0,len(A))
        for a in range(0,len(A)):
            out[a] = A[a] in B
        return out        

    def SearchRow(self):
        """Determine which row of GLOBAL.MOSL to search next; return an integer."""
        if len(GLOBAL.PLOS) == 0:
            return 0
        Row = range(0,GLOBAL.N_MOSL)
        for x in range (0,len(GLOBAL.PLOS)):
            Row = GLOBAL.Library.SetDiff(Row,GLOBAL.PLOS[x])
        return Row[0]
        
    def SearchOver(self, row):
        """Determine if the search is over by testing whether the current row is zero, and if each cell in the first row is a list for which each element has been terminated in GLOBAL.LTerm; return boolean."""
        if row == 0:
            for j in range(0,len(GLOBAL.MOSL[0])):
                if isinstance(GLOBAL.MOSL[0][j], list):
                    for k in range(0,len(GLOBAL.MOSL[0][j])):
                        if GLOBAL.LTerm[0][j][k] == 0:
                            return False
            return True
        return False
        
    def LooplistElements(self, Looplist):
        """Compute a list of all variables appearing in Looplist; return a list."""
        if len(Looplist) == 0:
            return [None]
        Elements = []
        for q in range(0,len(Looplist)):
            Elements = Elements+Looplist[q]
        return [GLOBAL.Library.Unique(Elements)]

    def GetSetSize(self):
        """Calculate the total number of variable in GLOBAL.PLOS; return an integer"""
        size = 0
        if len(GLOBAL.PLOS) == 0:
            return size
        else:
            for q in range(0,len(GLOBAL.PLOS)):
                size = size + len(GLOBAL.PLOS[q])
            return size

    def NextLoop(self, Row):
        """Determine the next loop in MOSL by insuring that it is not terminated in GLOBAL.LTerm, not [], >= len(GLOBAL.PLOS), and does not contain elements in GLOBAL.PLOS; return a list."""
        SSPLOS = GLOBAL.Library.GetSetSize()
        looplist = GLOBAL.Library.LooplistElements(GLOBAL.PLOS)
        for j in range(0,len(GLOBAL.MOSL[Row])):
            for k in range(0,len(GLOBAL.MOSL[Row][j])):
                candidates = GLOBAL.Library.Unique(GLOBAL.MOSL[Row][j][k])
                AA = (GLOBAL.LTerm[Row][j][k] == 0)
                BB = (GLOBAL.MOSL[Row][j][k][0] != None)
                CC = (len(GLOBAL.MOSL[Row][j][k]) <= GLOBAL.N_MOSL - SSPLOS)
                DD = (True not in GLOBAL.Library.IsElement(candidates,looplist[0]))
                if (GLOBAL.LTerm[Row][j][k] == 0) and (GLOBAL.MOSL[Row][j][k][0] != None) and (len(GLOBAL.MOSL[Row][j][k]) <= GLOBAL.N_MOSL - SSPLOS) and (True not in GLOBAL.Library.IsElement(candidates,looplist[0])):
                    return [GLOBAL.MOSL[Row][j][k]]+[[k]]
        return [None, None]

    def InitializeTerm(self):
        """Initialize a termination matrix for MOSL; modify GLOBAL.LTerm and return a list of lists."""
        N1 = len(GLOBAL.MOSL)
        GLOBAL.LTerm = deepcopy(GLOBAL.MOSL)
        for i in range(0, N1):
            for j in range(0, len(GLOBAL.MOSL[i])):
                K = range(0,len(GLOBAL.MOSL[i][j]))
                for k in range(0,len(GLOBAL.MOSL[i][j])):
                    K[k] = 0
                GLOBAL.LTerm[i][j] = K
        return GLOBAL.LTerm

    def InitializeMOSL(self, N):
        """Initialize and return a MOSL data structure of size N."""
        MOSL = range(0,N)
        for i in range(0,N):
            MOSL[i] = range(0,N-(i))
        for i in range(0,N):
            for j in range(0,N-(i)):
                MOSL[i][j] = [[None]]
        return MOSL

    def MakeMOSL(self, N):
        """Construct a Matrix Of Sets of Loops for use in pruning the search space of GLOBAL.LOL when searching for N-spanning disjoint loop sets; modify GLOBAL.MOSL"""
        GLOBAL.MOSL = GLOBAL.Library.InitializeMOSL(N)
        for a in range(0,len(GLOBAL.LOL)):
            FirstElement = GLOBAL.LOL[a][0]    # Row corresponds to value first element of the a-th loop
            LoopLength = len(GLOBAL.LOL[a])-2  # Col corresponds to length of the a-th loop minus two
            #                                    because counting starts at 0 and because loops initial 
            #                                    elements are represented at their terminus.
            if GLOBAL.MOSL[FirstElement][LoopLength] == [[None]]:
                GLOBAL.MOSL[FirstElement][LoopLength] = [GLOBAL.LOL[a][:-1]]
            else:
                GLOBAL.MOSL[FirstElement][LoopLength] = GLOBAL.MOSL[FirstElement][LoopLength]+[GLOBAL.LOL[a][:-1]]
            
    def MakeLoopENVY(self):
        """Determine which row to search in GLOBAL.MOSL for the next acceptable loop eliminating rows corresponding to variables already in GLOBAL.PLOS; return an integer."""
        N1 = len(GLOBAL.MOSL)
        if len(GLOBAL.PLOS) == 0:
            return range(0,N1)
        else:
            SearchRow = range(0, N1)
            for x in range(0,len(GLOBAL.PLOS)):
                SearchRow = GLOBAL.Library.SetDiff(SearchRow,GLOBAL.PLOS[x])
        return SearchRow

    def EnumerateSOSL(self, N):
        """Enumerate the Sets Of Spanning Loops using GLOBAL.MOSL, return a list of lists"""
        GLOBAL.N_MOSL = len(GLOBAL.MOSL)
        GLOBAL.LTerm = GLOBAL.Library.InitializeTerm()
        GLOBAL.PLOS = []
        SOSL = []
        k_last = []
        
        while True:
            Row = GLOBAL.Library.SearchRow()
     
            # is the search over?
            if GLOBAL.Library.SearchOver(Row):
                return SOSL

            # if there's no valid search row...
            if Row == []:
                return SOSL

            Loop = GLOBAL.Library.NextLoop(Row)
            # if there's no valid loop in the row and it is the first...
            if Loop[0] == None and Row == 0:
                return SOSL

            # if there's no valid loop in the row and it's not the first...
            if Loop[0] == None and Row != 0:

                # clear remaining loops
                for i in GLOBAL.Library.MakeLoopENVY():
                    for j in range(0,len(GLOBAL.MOSL[i])):
                        for k in range(0,len(GLOBAL.MOSL[i][j])):
                            GLOBAL.LTerm[i][j][k] = 0
        
                # clear the row in GLOBAL.Term
                i = Row
                j = len(GLOBAL.MOSL[i])-1
                for k in range(0,len(GLOBAL.MOSL[i][j])):
                    GLOBAL.LTerm[i][j][k] = 0
     
                # terminate the last loop in PLOS
                if GLOBAL.PLOS != []:
                    i = GLOBAL.PLOS[-1][0]
                    j = len(GLOBAL.PLOS[-1])
                    k = Loop[1]
                    for jj in range(0,j):
                        for kk in range(0,len(GLOBAL.LTerm[i][jj])):
                            if jj == j-1 and kk <= k_last[-1][0]:
                                GLOBAL.LTerm[i][jj][kk] = 1
                
                # remove the last loop from PLOS
                GLOBAL.PLOS = GLOBAL.PLOS[0:-1]

                k_last = k_last[0:-1]
                continue

            # add next.loop to PLOS
            if GLOBAL.PLOS == []:
                GLOBAL.PLOS = [Loop[0]]
            else:
                GLOBAL.PLOS = GLOBAL.PLOS+[Loop[0]]

            if k_last == []:
                k_last = [Loop[1]]
            else:
                k_last = k_last+ [Loop[1]]
         
            # test if PLOS spans N and add to SOSL if it does
            if GLOBAL.Library.GetSetSize() == N:

                # add PLOS to SOSL
                if SOSL == []:
                    SOSL = [GLOBAL.PLOS]
                else:
                    SOSL = SOSL+[GLOBAL.PLOS]

                # terminate the last loop in PLOS
                i = GLOBAL.PLOS[-1][0]
                j = len(GLOBAL.PLOS[-1])-1
                k = Loop[1]
                GLOBAL.LTerm[i][j][k_last[-1][0]] = 1

                # remove the last loop from PLOS
                GLOBAL.PLOS = GLOBAL.PLOS[0:-1]
                k_last = k_last[0:-1]
                continue

    def LoopProd(self, C, loop):
        """Calculate the qualitative path product of loop in subsystem C; return a sign."""
        lprod = 1
        if len(loop) > 1:
            for edge in range(0,len(loop)):
                if edge+1 < len(loop):
                    lprod = lprod * C[loop[edge+1]][loop[edge]]
                else:
                    lprod = lprod * C[loop[0]][loop[edge]]
        if len(loop) == 1:
            lprod = lprod * C[loop[0]][loop[0]]
        return lprod

    def SOSLProd(self, C, SOSL):
        """Calculate the qualitative product of SOSL in C; return a sign."""
        sprod = 1
        for loop in SOSL:
            sprod = sprod*GLOBAL.Library.LoopProd(C,loop)
        return sprod

    def Feedback(self, C):
        """Calculate the qualitative adjusted sum of products of SOSLs in C; return -1,0,1, or None"""
        N = len(C)

        if N == 1:
            return C[0][0]

        GLOBAL.LOL = GLOBAL.Library.EnumerateLoops(C)
        if GLOBAL.LOL == []:
            return 0

        Sum = 0
        GLOBAL.Library.MakeMOSL(N)
        sosl = GLOBAL.Library.EnumerateSOSL(N)
        for SOSL in sosl:
            
            adjust = (-1)**(len(SOSL)+1)
            sprod = GLOBAL.Library.SOSLProd(C,SOSL)*adjust
            if Sum == 0:
                Sum = sprod
            else:
                if Sum == (-1)*sprod:
                    return None
        return Sum

    def PathProd(self, CM, path):
        """Calculate the qualitative path product of path in subsystem C; return a sign."""
        pprod = CM[path[1]][path[0]]
        if len(path) == 2:
            if path[0] == path[1]:
                return 1
            return pprod
        for edge in range(1,(len(path)-1)):
            pprod = pprod * CM[path[edge+1]][path[edge]]
        return pprod

    def CompSlice(self, CM, Compliment):
        """Construct a matrix corresponding to the complementary subsytem C in CM; return a list of lists."""
        CompN = len(Compliment)
        CompCM = [range(0,CompN)]
        for i in range(0,CompN-1):
            CompCM = CompCM + [range(0,CompN)]
        for i in range(0,CompN):
            for j in range(0,CompN):
                CompCM[i][j] = int(CM[Compliment[i]][Compliment[j]])
        return CompCM

    def Bitmask(Pij):
        """Calculate the bitmask of Pij; return an integer."""
        bitmask = 0
        for index in range(0,len(Pij)):
            return bitmask + (2**(Pij[index] - 1))

    def SUM_Path_x_FofC(self, CM, i, j):
        """Calculates the qualitative sum of products of paths to i from j times the feedback of their respective compelmentary subsystems; returns -1, 0, 1, or None."""
        N = GLOBAL.N
        Sum = 0
        for path in CM.Paths[i][j]:
            # if the complimentary subsystem C has zero elements, assign F.C -1
            C = GLOBAL.Library.PathCompliment(path,N)
            if len(C) == 0:
                F_C = -1
            # otherwise, produce feedback F_C from the complimentary subsystem C
            else:
                F_C = GLOBAL.Library.Feedback(GLOBAL.Library.CompSlice(CM.A,C))
                if F_C == None:
                    return None
            pprod = GLOBAL.Library.PathProd(CM.A,path)
            P_F_C = pprod*F_C
            # if this is the first time through the loop
            if Sum == 0:
                Sum = P_F_C
            else:
                if Sum == (-1)*P_F_C:
                    return None
        return Sum

    def MakeCEM(CM):
        """Compute the community effect matrix of the supplied community matrix CM; return list (of lists)"""
        if frame.ListBox.GetCount() > 0:
            index = deepcopy(int(frame.ListBox.GetSelection()))
            CM = GLOBAL.Library.CommunityMatrices[index]
            if ( (hasattr(CM, "CEMFlag") == False) or (GLOBAL.Library.PrefsCEM == True and CM.CEMFlag == False) ):
                if hasattr(CM, "CEMFlag") == False:
                    GLOBAL.Library.PrefsCEM = True
                GLOBAL.N = len(CM.A)
                N = GLOBAL.N
                dfdc = 1
                F_N = -1
                SUM = 1
                # create an initial CEM
                CEM = GLOBAL.Library.SquareMatrix(N)
                for i in range(0,N):
                    for j in range(0,N):
                        CM.Paths[i][j] = GLOBAL.Library.EnumeratePaths(CM.A,i,j)
                        Sum = GLOBAL.Library.SUM_Path_x_FofC(CM,i,j)
                        if Sum == None:
                            CEM[j][i] = None
                        else:
                            CEM[j][i] = Sum/F_N
                CM.CEM = GLOBAL.Library.Transpose(CEM)
                CM.CEMFlag = True


    def MakeCorrelations(self):
        """Calculate correlation matrices"""

        def QualProduct(A,B):
            """Calculate the product of -1,0,1, and -1/1"""
            if (A == None or B == None):
                return None
            else:
                return A*B
                
        if frame.ListBox.GetCount() > 0:
            index = deepcopy(int(frame.ListBox.GetSelection()))
            CM = GLOBAL.Library.CommunityMatrices[index]
            CEM = CM.CEM
            if ( (hasattr(CM, "CorrelationsFlag") == False) or (GLOBAL.Library.PrefsCEM == True and CM.CorrelationsFlag == False) ):
                if hasattr(CM, "CorrelationsFlag") == False:
                    GLOBAL.Library.PrefsCorrelations = True
                GLOBAL.N = len(CM.A)
                N = GLOBAL.N
                # create N initial correlation matrices
                Correlations = range(0,N)
                for i in range(0,N):
                    Correlations[i] = GLOBAL.Library.SquareMatrix(N)
                for corr in range(0,N):
                    #populate upper diagonal
                    for i in range(0,N):
                        for j in range(0,N):
                            if j>= i:
                                Correlations[corr][i][j] = QualProduct(CEM[corr][i], CEM[corr][j])
                            else:
                                Correlations[corr][i][j] = 2
                CM.Correlations = Correlations
                CM.CorrelationsFlag = True


    def AdjointFeedback(self, C):
        """Calculate the qualitative adjusted sum of products of SOSLs in C under Dambacher's assumption of unit feedback; return a signed integer"""
        N = len(C)
        if N == 1:
            return -1*C[0][0]
        GLOBAL.LOL = GLOBAL.Library.EnumerateLoops(C)
        if GLOBAL.LOL == []:
            return 0
        Sum = 0
        GLOBAL.Library.MakeMOSL(N)
        sosl = GLOBAL.Library.EnumerateSOSL(N)
        for SOSL in sosl:
            adjust = (-1)**(len(SOSL)+1)
            sprod = GLOBAL.Library.SOSLProd(C,SOSL)*adjust
            # This line is what makes this calculation an Adjoint calculation
            Sum = Sum + sprod
        return -1*Sum

    def AdjointSUM_Path_x_FofC(self, CM, i, j):
        """Calculates the qualitative sum of products of paths to i from j times the feedback of their respective compelmentary subsystems under Dambacher's assumption of unit feedback; returns a signed integer."""
        N = GLOBAL.N
        Adj = 0
        for path in CM.Paths[i][j]:

            # Produce the Adjoint for a specific P.ij named Adj if the complimentary 
            # subsystem C has zero elements, increment Adj by the path product
            C = GLOBAL.Library.PathCompliment(path,N)
            if len(C) == 0:
                Adj = Adj + GLOBAL.Library.PathProd(CM.A,path)

            # otherwise, increment Adj.ij by the summed feedback times the path product.
            else:
                Adj = Adj + GLOBAL.Library.AdjointFeedback(GLOBAL.Library.CompSlice(CM.A,C))*GLOBAL.Library.PathProd(CM.A,path)
        return Adj

    def MakeAdjoint(self):
        """Compute the classical adjoint matrix of the supplied community matrix CM; return list (of lists)"""
        if frame.ListBox.GetCount() > 0:
            index = deepcopy(int(frame.ListBox.GetSelection()))
            CM = GLOBAL.Library.CommunityMatrices[index]
            if ( (GLOBAL.Library.PrefsAdjoint == True and hasattr(CM, "AdjointFlag") == False) or (GLOBAL.Library.PrefsAdjoint == True and CM.AdjointFlag == False) ):
                if hasattr(CM, "AdjointFlag") == False:
                    GLOBAL.Library.PrefsAdjoint = True
                if frame.ListBox.GetCount() > 0:
                    index = deepcopy(int(frame.ListBox.GetSelection()))
                    CM = GLOBAL.Library.CommunityMatrices[index]
                    if GLOBAL.Library.PrefsAdjoint == True and CM.AdjointFlag == False:
                        GLOBAL.N = len(CM.A)
                        N = GLOBAL.N
                        F_N = -1
                        SUM = 1
                        # create an initial CEM
                        Adjoint = [range(0,N)]
                        for i in range(0,N-1):
                            Adjoint = Adjoint + [range(0,N)]
                        for i in range(0,N):
                            for j in range(0,N):
                                Adjoint[j][i] = GLOBAL.Library.AdjointSUM_Path_x_FofC(CM,i,j)
                        CM.Adjoint = Adjoint
                        CM.AdjointFlag = True


    def TotalFeedback(self, C):
        """Return the total number of loops in SOSL\n\n(with a few computational shortcuts for special cases)."""
        N = len(C)
        if N == 1:
            return abs(C[0][0])
        GLOBAL.LOL = GLOBAL.Library.EnumerateLoops(C)
        if GLOBAL.LOL == []:
            return 0
        Sum = 0
        GLOBAL.Library.MakeMOSL(N)
        sosl = GLOBAL.Library.EnumerateSOSL(N)
        return len(sosl)

    def TotalSUM_Path_x_FofC(self, CM, i, j):
        """Calculates the total levels of feedback associated with all paths to i from j from the feedback of their respective compelmentary subsystems; returns an unsigned integer."""
        N = GLOBAL.N
        T = 0
        for path in CM.Paths[i][j]:

            # produce T for a specific P.ij named T if the complimentary subsystem C has 
            # zero elements, increment T by 1
            C = GLOBAL.Library.PathCompliment(path,N)
            if len(C) == 0:
                T = T + 1

            # otherwise, increment T by the absolute number of feedback levels
            else:
                T = T + GLOBAL.Library.TotalFeedback(GLOBAL.Library.CompSlice(CM.A,C))
        return T

    def MakeT(self):
        """Compute the total feedback matrix of the supplied community matrix CM; return list (of lists)"""
        if frame.ListBox.GetCount() > 0:
            index = deepcopy(int(frame.ListBox.GetSelection()))
            CM = GLOBAL.Library.CommunityMatrices[index]
            if ( (hasattr(CM, "TFlag") == False) or (GLOBAL.Library.PrefsT == True and CM.TFlag == False) ):
                if hasattr(CM, "TFlag") == False:
                    GLOBAL.Library.PrefsT = True
                if frame.ListBox.GetCount() > 0:
                    index = deepcopy(int(frame.ListBox.GetSelection()))
                    CM = GLOBAL.Library.CommunityMatrices[index]
                    if GLOBAL.Library.PrefsT == True and CM.TFlag == False:
                        GLOBAL.N = len(CM.A)
                        N = GLOBAL.N
                        F_N = -1
                        SUM = 1
                        # create an initial CEM
                        Total = [range(0,N)]
                        for i in range(0,N-1):
                            Total = Total + [range(0,N)]
                        for i in range(0,N):
                            for j in range(0,N):
                                Total[j][i] = GLOBAL.Library.TotalSUM_Path_x_FofC(CM,i,j)
                        CM.T = Total
                        CM.TFlag = True


    ##########
    # FUNCTION: MakeWFM
    # Produce the weighted feedback matrix = abs(Adjoint)/T (element-wise)
    def MakeWFM(self):
    
        if frame.ListBox.GetCount() > 0:
            
            # Make weighted feedback matrix
            index = deepcopy(int(frame.ListBox.GetSelection()))
            CM = GLOBAL.Library.CommunityMatrices[index]
            if ( (hasattr(CM, "WFMFlag") == False) or (GLOBAL.Library.PrefsWFM == True and CM.WFMFlag == False) ):
                if hasattr(CM, "WFMFlag") == False:
                    GLOBAL.Library.PrefsWFM = True
                WFM = deepcopy(CM.Adjoint)
                T = deepcopy(CM.T)
                N = len(WFM)
                for i in range(0, N):
                    for j in range(0, N):
                        if T[i][j] != 0:
                            WFM[i][j] = fix(abs(float(WFM[i][j]))/T[i][j],GLOBAL.WeightedFeedbackPrecision)
                        else:
                            WFM[i][j] = fix(1.00000000,GLOBAL.WeightedFeedbackPrecision)
                CM.WFM = WFM
                CM.WFMFlag = True    


    def MakeWPM(self):
        """Compute the weighted prediction matrix of the supplied community matrix CM; return list (of lists)"""
        if frame.ListBox.GetCount() > 0:
            index = deepcopy(int(frame.ListBox.GetSelection()))
            CM = GLOBAL.Library.CommunityMatrices[index]
            Adjoint = deepcopy(CM.Adjoint)
            if ( (hasattr(CM,"WPMFlag") == False) or (GLOBAL.Library.PrefsWPM == True and CM.WPMFlag == False) ):
                if hasattr(CM, "WPMFlag") == False:
                    GLOBAL.Library.PrefsWPM = True
                WPM = deepcopy(CM.CEM)
                N = len(CM.CEM)
                for i in range(0, N):
                    for j in range(0, N):
                        if GLOBAL.ThresholdCriterion == 0:
                            if WPM[i][j] == None and float(CM.WFM[j][i]) > GLOBAL.WeightedPredictionThreshold:
                                WPM[i][j] = sign(Adjoint[j][i])*2
                        if GLOBAL.ThresholdCriterion == 1:
                            if WPM[i][j] == None and float(CM.WFM[j][i]) >= GLOBAL.WeightedPredictionThreshold:
                                WPM[i][j] = sign(Adjoint[j][i])*2
                CM.WPM = WPM
                CM.WPMFlag = True


    def MakeCLEM(self):
        """Compute the change in life expectancy matrix of the supplied community matrix CM; return list (of lists)"""
        if frame.ListBox.GetCount() > 0:
            # Make births and deaths matrices
            index = deepcopy(int(frame.ListBox.GetSelection()))
            CM = GLOBAL.Library.CommunityMatrices[index]
            N = len(CM.A)
            if ( (hasattr(CM, "CLEMFlag") == False) or (GLOBAL.Library.PrefsCLEM == True and CM.CEMFlag == True and CM.CLEMFlag == False) ):
                if hasattr(CM, "CLEMFlag") == False:
                    GLOBAL.Library.PrefsCLEM = True
                B = deepcopy(CM.A)
                D = deepcopy(CM.A)
                for i in range(0, N):
                    for j in range(0, N):
                        if B[i][j] < 0:
                            B[i][j] = 0
                        D[i][j] = B[i][j] - CM.A[i][j]
                B = array(B,dtype='intp')  # Births
                D = array(D,dtype='intp')  # Deaths
                TCEM = array(deepcopy(CM.Adjoint),dtype='intp')  #Transpose adjoint
                CLEMB = sign(dot(-B,TCEM))
                CLEMD = sign(dot(-D,TCEM))
                CLEM = deepcopy(CM.Adjoint)
                for i in range(0,N):
                    for j in range(0, N):
                        CLEM[i][j] = CLEMB[i][j]
                    CLEM[i][i] =CLEMD[i][i],CLEM[i][i]
                CM.CLEM = CLEM
                CM.CLEMFlag = True
    
    pass
    
# Class for community matrix creation variables
class NewCM:
    Name = GLOBAL.language["main_NewCMName"][0]
    N = None
    pass

################################################################################
### wxWidgets GUI INTERFACE                                                  ###
################################################################################

########################################
# Class for the main GUI

##class AppUI(Frame):
class AppUI(wx.Frame):

    def __init__(self, parent, id, title):

        # deal with paths
        wx.GetApp().SetAppName("Loop Analyst")
        self.Preferences = str(wx.StandardPaths.Get().GetUserConfigDir())+"/Loop Analyst.prefs"
        # Load the preferences file, if available
        if exists(self.Preferences):
            Prefs = file(self.Preferences,'r')
            PERSISTENT.Persistence = load(Prefs)
            Prefs.close()
            GLOBAL.RecentDirectory = deepcopy(PERSISTENT.Persistence[0])
            GLOBAL.RecentLibraries = deepcopy(PERSISTENT.Persistence[1])
            GLOBAL.RecentLibrariesListLength = deepcopy(PERSISTENT.Persistence[2])
            if len(PERSISTENT.Persistence) > 3:
                GLOBAL.GraphColoring = PERSISTENT.Persistence[3]
            else:
                GLOBAL.GraphColoring = 0
            if len(PERSISTENT.Persistence) > 4:
                GLOBAL.DisplayFontSize = PERSISTENT.Persistence[4]
            else:
                GLOBAL.DisplayFontSize = 24
            if len(PERSISTENT.Persistence) > 6:
                GLOBAL.WeightedPredictionThreshold = PERSISTENT.Persistence[5]
                GLOBAL.ThresholdCriterion = PERSISTENT.Persistence[6]
            else:
                GLOBAL.WeightedPredictionThreshold = 0.5
                GLOBAL.ThresholdCriterion = 1
            if len(PERSISTENT.Persistence) > 8:
                GLOBAL.Position = PERSISTENT.Persistence[7]
                GLOBAL.Size = PERSISTENT.Persistence[8]
            else:
                GLOBAL.Position = (0, 22)
                GLOBAL.Size = (1078,600)
            if len(PERSISTENT.Persistence) > 9:
                GLOBAL.WeightedFeedbackPrecision = PERSISTENT.Persistence[9]
            else:
                GLOBAL.WeightedFeedbackPrecision = 1
            if len(PERSISTENT.Persistence) > 10:
                GLOBAL.dotLocation = PERSISTENT.Persistence[10]
            else:
                GLOBAL.dotLocation = ""
            if len(PERSISTENT.Persistence) > 11:
                GLOBAL.Language = PERSISTENT.Persistence[11]
            else:
                GLOBAL.Language = 0

        # Splash screen
        #Splash = self.getBitmap()
        #wx.SplashScreen(Splash, wx.SPLASH_CENTRE_ON_SCREEN | wx.SPLASH_TIMEOUT, 2000, None, -1)
        #wx.Yield()

        wx.Frame.__init__(self, parent, wx.NewId(), title="Loop Analyst: "+GLOBAL.LibraryName, style=wx.DEFAULT_FRAME_STYLE | wx.RESIZE_BOX, size=GLOBAL.Size, pos = GLOBAL.Position)

        # Get path to Loop Analyst.py
        LApath = split(realpath(__file__))[0]

        # Set the language internationalization
        if GLOBAL.Language == 0:
            if exists(LApath+'/localizations/en-us.localization'):
                GLOBAL.language = load(file(LApath+'/localizations/en-us.localization',"r"))
        if GLOBAL.Language == 1:
            if exists(LApath+'/localizations/en-uk.localization'):
                GLOBAL.language = load(file(LApath+'/localizations/en-uk.localization',"r"))

        ##########
        # Add the widgets!
        # make the menu bar and menus!
        self.Menubar()
        # Lay it all on out!
        self.UILayout()
        
        TEMPORARY = GLOBAL.IconData
        GLOBAL.IconData = GLOBAL.SplashData
        About = AboutDialog(self, -1, "", style=wx.DEFAULT_DIALOG_STYLE | wx.STAY_ON_TOP)
        About.CenterOnScreen()
        About.Bind(wx.EVT_CHAR_HOOK, None)
        About.ShowModal()
        About.GetChildren()[5].SetFocus()
        About.Destroy()
        GLOBAL.IconData = TEMPORARY
        self.Raise()
        Launch = False


    ############################################################################
    ### AppUI INTERFACE WIDGET FUNCTIONS AND CLASSES                        ###
    ############################################################################

    ##########
    # WIDGETS: UILayout
    def UILayout(self):
        # top-level is a panel of two columns
        # left panel is a panel of two rows, statically sized
        # the left-top panel is statically sized, and contains a horizontal 
        #   arrangement of three Buttons
        # the left-bottom panel is a ListBox
        # the right panel is dynamically sized, and contains an AuiNotebook

        ##########
        # bottoms up! the bottom level objects defined here .  .  .

        ##########
        # Buttons
        self.NewButton = wx.Button(self, wx.NewId(), '&New', (-1, -1), wx.DefaultSize)
        self.NewButton.SetDefault()
        self.NewButton.SetToolTipString(GLOBAL.language["main_AppUINewButton"][0])
        self.Bind(wx.EVT_BUTTON, self.NewCM, self.NewButton)

        self.EditButton = wx.Button(self, wx.NewId(), '&Edit', (-1, -1), wx.DefaultSize) # cmd: self.EditCM
        self.EditButton.SetToolTipString(GLOBAL.language["main_AppUIEditButton"][0])
        self.Bind(wx.EVT_BUTTON, self.EditCM, self.EditButton)

        self.DelButton = wx.Button(self, wx.NewId(), '&Delete', (-1, -1), wx.DefaultSize) # cmd: self.DelCM
        self.DelButton.SetToolTipString(GLOBAL.language["main_AppUIDeleteButton"][0])
        self.Bind(wx.EVT_BUTTON, self.DeleteCM, self.DelButton)

        ##########
        # ListBox
        self.ListBox = wx.ListBox(self, 60, (100,50), (90,120), list(),wx.LB_SINGLE | wx.LB_NEEDED_SB)
        self.Bind(wx.EVT_LISTBOX, self.EvtListBox, self.ListBox)
        self.Bind(wx.EVT_LISTBOX_DCLICK, self.EvtListBoxDClick, self.ListBox)
        
        ##########
        # Notebook
        text = "" # this is sample text
        self.Notebook = wx.aui.AuiNotebook(self, style = 0)
        self.Notebook.SetCanFocus(True)

        #####
        # Community Matrix Page
        self.Page1 = wx.Window(self.Notebook, wx.NewId())
        self.PageCM = wx.StaticText(self.Page1, wx.NewId(), self.ReviseCMText(), style=wx.TE_MULTILINE)
        self.Notebook.AddPage(self.Page1, GLOBAL.language["main_AppUIPageCM"][0])

        #####
        # Graph Display Page
        self.Page2 = wx.Window(self.Notebook, wx.NewId())
        self.Notebook.AddPage(self.Page2, GLOBAL.language["main_AppUIPageGraph"][0])

        #####
        # Community Effect Matrix Page
        self.Page3 = wx.Window(self.Notebook, wx.NewId())
        self.PageCEM = wx.StaticText(self.Page3, wx.NewId(), self.ReviseCEMText(), style=wx.TE_MULTILINE)
        self.Notebook.AddPage(self.Page3, GLOBAL.language["main_AppUIPagePredictions"][0])

        #####
        # Weighted Adjoint and Total Feedback Matrices Page
        self.Page4 = wx.Window(self.Notebook, wx.NewId())
        self.PageAdjoint = wx.StaticText(self.Page4, wx.NewId(), self.ReviseAdjointText(), style=wx.TE_MULTILINE)
        self.Notebook.AddPage(self.Page4, GLOBAL.language["main_AppUIPageAdjointT"][0])

        #####
        # Weighted Feedback Matrix Page
        self.Page5 = wx.Window(self.Notebook, wx.NewId())
        self.PageWFM = wx.StaticText(self.Page5, wx.NewId(), self.ReviseWFMText(), style=wx.TE_MULTILINE)
        self.Notebook.AddPage(self.Page5, GLOBAL.language["main_AppUIPageWFM"][0])

        #####
        # Weighted Predictions Matrix Page
        self.Page6 = wx.Window(self.Notebook, wx.NewId())
        self.PageWPM = wx.StaticText(self.Page6, wx.NewId(), self.ReviseWPMText(), style=wx.TE_MULTILINE)
        self.Notebook.AddPage(self.Page6, GLOBAL.language["main_AppUIPageWFP"][0])

        #####
        # Change in Life Expectancy Matrix Page
        self.Page7 = wx.Window(self.Notebook, wx.NewId())
        self.PageCLE = wx.StaticText(self.Page7, wx.NewId(), self.ReviseCLEMText(), style=wx.TE_MULTILINE)
        self.Notebook.AddPage(self.Page7, GLOBAL.language["main_AppUIPageLE"][0])

        ##########
        # Layout
        Border = 5
        self.ButtonBox = wx.BoxSizer(wx.HORIZONTAL)
        self.ButtonBox.Add(self.NewButton, 1, wx.LEFT | wx.ALL, border=Border)
        self.ButtonBox.Add(self.EditButton, 1, wx.CENTER | wx.ALL, border=Border)
        self.ButtonBox.Add(self.DelButton, 1, wx.RIGHT | wx.ALL, border=Border)
        
        self.Controls = wx.BoxSizer(wx.VERTICAL)
        self.Controls.Add(self.ButtonBox, 0, wx.EXPAND | wx.ALL, Border)
        self.Controls.Add(self.ListBox, 1, wx.EXPAND | wx.ALL, Border)

        self.Display = wx.BoxSizer(wx.VERTICAL)
        self.Display.Add(self.Notebook, 1, wx.EXPAND | wx.ALL, 0)

        self.Tippy = wx.BoxSizer(wx.HORIZONTAL)
        self.Tippy.Add(self.Controls, 0, wx.EXPAND | wx.ALL, 0)
        self.Tippy.Add(self.Display, 1, wx.EXPAND | wx.ALL, Border+2)
        self.Tippy.SetMinSize((1078,600))
        self.SetSizerAndFit(self.Tippy)
        self.SetSize(GLOBAL.Size)

        self.Bind(wx.EVT_CHAR_HOOK, self.OnChar)
        #self.Bind(wx.EVT_SIZE, self.UpdateDisplay)
        #wx.EVT_CHAR(self, self.OnChar)

        #self.Bind(wx.EVT_SIZE, self.EvtListBox)
        self.Show()

    ##########
    # WIDGET: Menubar
    def Menubar(self):

        # Set up menuitem IDs
        ID_UNDO=wx.NewId()
        ID_REDO=wx.NewId()
        ID_NEWCM=wx.NewId()
        ID_NEWLIB=wx.NewId()
        ID_OPEN=wx.NewId()
        ID_RECENT=wx.NewId()
        ID_RECENT1=wx.NewId()
        ID_RECENT2=wx.NewId()
        ID_RECENT3=wx.NewId()
        ID_RECENT4=wx.NewId()
        ID_RECENT5=wx.NewId()
        ID_RECENT6=wx.NewId()
        ID_RECENT7=wx.NewId()
        ID_RECENT8=wx.NewId()
        ID_RECENT9=wx.NewId()
        ID_RECENT10=wx.NewId()
        ID_CLEARLIBS=wx.NewId()
        ID_APPEND=wx.NewId()
        ID_SAVE=wx.NewId()
        ID_SAVEAS=wx.NewId()
        ID_SAVEGR=wx.NewId()
        ID_IMPCM=wx.NewId()
        ID_EXPAN=wx.NewId()
#        ID_EXPLIB=wx.NewId()
        ID_EXPGPH=wx.NewId()
        ID_REVERT=wx.NewId()
        ID_PPREFS=wx.ID_PREFERENCES
        ID_LPREFS=wx.NewId()
        ID_QUIT=wx.ID_EXIT
        ID_CUTCM=wx.NewId()
        ID_COPYCM=wx.NewId()
        ID_PASTECM=wx.NewId()
        ID_DELCM=wx.NewId()
        ID_DUPECM=wx.NewId()
        ID_EDITCM=wx.NewId()
        ID_CLIPCM=wx.NewId()
        ID_CLIPGR=wx.NewId()
        ID_CLIPPR=wx.NewId()
        ID_CLIPAT=wx.NewId()
        ID_CLIPWF=wx.NewId()
        ID_CLIPWP=wx.NewId()
        ID_CLIPLE=wx.NewId()
        ID_CLIPAN=wx.NewId()
        ID_CLIPCO=wx.NewId()
        ID_CLIPPA=wx.NewId()
        ID_CLIPLP=wx.NewId()
        ID_HELP=wx.ID_HELP
        ID_ABOUT=wx.ID_ABOUT

        # File menu
        filemenu = wx.Menu()
        filemenu.Append(ID_UNDO, GLOBAL.language["menu_ID_UNDO"][0][0],GLOBAL.language["menu_ID_UNDO"][0][1])
        filemenu.Append(ID_REDO, GLOBAL.language["menu_ID_REDO"][0][0],GLOBAL.language["menu_ID_REDO"][0][1])
        filemenu.AppendSeparator()
        filemenu.Append(ID_NEWCM, GLOBAL.language["menu_ID_NEWCM"][0][0],GLOBAL.language["menu_ID_NEWCM"][0][1])
        filemenu.Append(ID_NEWLIB, GLOBAL.language["menu_ID_NEWLIB"][0][0],GLOBAL.language["menu_ID_NEWLIB"][0][1])
        filemenu.Append(ID_OPEN, GLOBAL.language["menu_ID_OPEN"][0][0],GLOBAL.language["menu_ID_OPEN"][0][1])
        filesubmenu = wx.Menu()
        filesibmenuIDs = [ID_RECENT1,ID_RECENT2,ID_RECENT3,ID_RECENT4,ID_RECENT5,ID_RECENT6,ID_RECENT7,ID_RECENT8,ID_RECENT9,ID_RECENT10]
        if len(GLOBAL.RecentLibraries) > 0:
            RecentLibraryNames = self.RecentMenuEntries(GLOBAL.RecentLibraries)
            for i in range(0,len(GLOBAL.RecentLibraries)):
                filesubmenu.Append(filesibmenuIDs[i], RecentLibraryNames[i])
            filesubmenu.AppendSeparator()
            filesubmenu.Append(ID_CLEARLIBS, GLOBAL.language["menu_ID_CLEARLIBS"][0][0])
        filemenu.AppendMenu(ID_RECENT, GLOBAL.language["menu_ID_RECENT"][0][0], filesubmenu)
        filemenu.Append(ID_APPEND, GLOBAL.language["menu_ID_APPEND"][0][0],GLOBAL.language["menu_ID_APPEND"][0][1])
        filemenu.Append(ID_SAVE, GLOBAL.language["menu_ID_SAVE"][0][0],GLOBAL.language["menu_ID_SAVE"][0][1])
        filemenu.Append(ID_SAVEAS, GLOBAL.language["menu_ID_SAVEAS"][0][0],GLOBAL.language["menu_ID_SAVEAS"][0][1])
        filemenu.Append(ID_SAVEGR, GLOBAL.language["menu_ID_SAVEGR"][0][0],GLOBAL.language["menu_ID_SAVEGR"][0][1])
        filemenu.AppendSeparator()
        filemenu.Append(ID_IMPCM, GLOBAL.language["menu_ID_IMPCM"][0][0],GLOBAL.language["menu_ID_IMPCM"][0][1])
        filemenu.Append(ID_EXPAN, GLOBAL.language["menu_ID_EXPAN"][0][0],GLOBAL.language["menu_ID_EXPAN"][0][1])
#        filemenu.Append(ID_EXPLIB, GLOBAL.language["menu_ID_EXPLIB"][0][0],GLOBAL.language["menu_ID_EXPLIB"][0][1])
        filemenu.Append(ID_EXPGPH, GLOBAL.language["menu_ID_EXPGPH"][0][0],GLOBAL.language["menu_ID_EXPGPH"][0][1])
        filemenu.AppendSeparator()
        filemenu.Append(ID_REVERT, GLOBAL.language["menu_ID_REVERT"][0][0],GLOBAL.language["menu_ID_REVERT"][0][1])
#        filemenu.AppendSeparator()
        filemenu.Append(ID_PPREFS, GLOBAL.language["menu_ID_PPREFS"][0][0],GLOBAL.language["menu_ID_PPREFS"][0][1])
#        filemenu.Append(ID_LPREFS, GLOBAL.language["menu_ID_LPREFS"][0][0],GLOBAL.language["menu_ID_LPREFS"][0][1])
#        filemenu.AppendSeparator()
        filemenu.Append(ID_QUIT, GLOBAL.language["menu_ID_QUIT"][0][0],GLOBAL.language["menu_ID_QUIT"][0][1])
#        filemenu.AppendSeparator()

        # Edit menu
        editmenu = wx.Menu()
        editmenu.Append(ID_CUTCM, GLOBAL.language["menu_ID_CUTCM"][0][0],GLOBAL.language["menu_ID_CUTCM"][0][1])
        editmenu.Append(ID_COPYCM, GLOBAL.language["menu_ID_COPYCM"][0][0],GLOBAL.language["menu_ID_COPYCM"][0][1])
        editmenu.Append(ID_PASTECM, GLOBAL.language["menu_ID_PASTECM"][0][0],GLOBAL.language["menu_ID_PASTECM"][0][1])
        editmenu.Append(ID_DELCM, GLOBAL.language["menu_ID_DELCM"][0][0],GLOBAL.language["menu_ID_DELCM"][0][1])
        editmenu.Append(ID_DUPECM, GLOBAL.language["menu_ID_DUPECM"][0][0],GLOBAL.language["menu_ID_DUPECM"][0][1])
        editmenu.Append(ID_EDITCM, GLOBAL.language["menu_ID_EDITCM"][0][0],GLOBAL.language["menu_ID_EDITCM"][0][1])

        # Analysis menu
        analmenu = wx.Menu()
        analmenu.Append(ID_CLIPCM, GLOBAL.language["menu_ID_CLIPCM"][0][0],GLOBAL.language["menu_ID_CLIPCM"][0][1])
        analmenu.Append(ID_CLIPGR, GLOBAL.language["menu_ID_CLIPGR"][0][0],GLOBAL.language["menu_ID_CLIPGR"][0][1])
        analmenu.Append(ID_CLIPPR, GLOBAL.language["menu_ID_CLIPPR"][0][0],GLOBAL.language["menu_ID_CLIPPR"][0][1])
        analmenu.Append(ID_CLIPAT, GLOBAL.language["menu_ID_CLIPAT"][0][0],GLOBAL.language["menu_ID_CLIPAT"][0][1])
        analmenu.Append(ID_CLIPWF, GLOBAL.language["menu_ID_CLIPWF"][0][0],GLOBAL.language["menu_ID_CLIPWF"][0][1])
        analmenu.Append(ID_CLIPWP, GLOBAL.language["menu_ID_CLIPWP"][0][0],GLOBAL.language["menu_ID_CLIPWP"][0][1])
        analmenu.Append(ID_CLIPLE, GLOBAL.language["menu_ID_CLIPLE"][0][0],GLOBAL.language["menu_ID_CLIPLE"][0][1])
        analmenu.Append(ID_CLIPAN, GLOBAL.language["menu_ID_CLIPAN"][0][0],GLOBAL.language["menu_ID_CLIPAN"][0][1])
        analmenu.Append(ID_CLIPCO, GLOBAL.language["menu_ID_CLIPCO"][0][0],GLOBAL.language["menu_ID_CLIPCO"][0][1])
        analmenu.Append(ID_CLIPPA, GLOBAL.language["menu_ID_CLIPPA"][0][0],GLOBAL.language["menu_ID_CLIPPA"][0][1])
        analmenu.Append(ID_CLIPLP, GLOBAL.language["menu_ID_CLIPLP"][0][0],GLOBAL.language["menu_ID_CLIPLP"][0][1])

        # Help menu
        helpmenu = wx.Menu()
        helpmenu.Append(ID_HELP, GLOBAL.language["menu_ID_HELP"][0][0],GLOBAL.language["menu_ID_HELP"][0][1])
        helpmenu.Append(ID_ABOUT, GLOBAL.language["menu_ID_ABOUT"][0][0],GLOBAL.language["menu_ID_ABOUT"][0][1])

        # Create the menu
        MenuBar = wx.MenuBar()
        MenuBar.Append(filemenu,GLOBAL.language["menu_File"][0]) # Adding the "filemenu" to the MenuBar
        MenuBar.Append(editmenu,GLOBAL.language["menu_Edit"][0]) # Adding the "editmenu" to the MenuBar
        MenuBar.Append(analmenu,GLOBAL.language["menu_Analysis"][0]) # Adding the "analmenu" to the MenuBar
        MenuBar.Append(helpmenu,GLOBAL.language["menu_Help"][0]) # Adding the "helpmenu" to the MenuBar
        self.SetMenuBar(MenuBar)  # Adding the MenuBar to the Frame content.

        ##########
        # Ghosted menu items (i.e. my ToDo list!!!)
#        self.MenuBar.Enable(ID_IMPCM,False)
#        self.MenuBar.Enable(ID_EXPLIB,False)
        if GLOBAL.Library.PrefsGraph == False:
            self.MenuBar.Enable(ID_EXPGPH,False)
            self.MenuBar.Enable(ID_CLIPGR,False)
#        self.MenuBar.Enable(ID_LPREFS,False)
#        self.MenuBar.Enable(ID_HELP,False)

        ##########
        # Event handlers for "filemenu"
        wx.EVT_MENU(self, ID_UNDO, self.Undo)
        wx.EVT_MENU(self, ID_REDO, self.Redo)
        wx.EVT_MENU(self, ID_NEWCM, self.NewCM)
        wx.EVT_MENU(self, ID_NEWLIB, self.NewLibrary)
        wx.EVT_MENU(self, ID_OPEN, self.OpenLibraryDialog)
        wx.EVT_MENU(self, ID_RECENT1, self.OpenRecents1)
        wx.EVT_MENU(self, ID_RECENT2, self.OpenRecents2)
        wx.EVT_MENU(self, ID_RECENT3, self.OpenRecents3)
        wx.EVT_MENU(self, ID_RECENT4, self.OpenRecents4)
        wx.EVT_MENU(self, ID_RECENT5, self.OpenRecents5)
        wx.EVT_MENU(self, ID_RECENT6, self.OpenRecents6)
        wx.EVT_MENU(self, ID_RECENT7, self.OpenRecents7)
        wx.EVT_MENU(self, ID_RECENT8, self.OpenRecents8)
        wx.EVT_MENU(self, ID_RECENT9, self.OpenRecents9)
        wx.EVT_MENU(self, ID_RECENT10, self.OpenRecents10)
        wx.EVT_MENU(self, ID_CLEARLIBS, self.ClearRecents)
        wx.EVT_MENU(self, ID_APPEND, self.AppendLibraryDialog)
        wx.EVT_MENU(self, ID_SAVE, self.SaveLibrary)
        wx.EVT_MENU(self, ID_SAVEAS, self.SaveAsLibraryDialog)
        wx.EVT_MENU(self, ID_SAVEGR, self.SaveGraph)
        wx.EVT_MENU(self, ID_IMPCM, self.ImportCMDialog)
        wx.EVT_MENU(self, ID_EXPAN, self.ExportAnalysis)
        wx.EVT_MENU(self, ID_EXPGPH, self.ExportGraph)
        wx.EVT_MENU(self, ID_REVERT, self.RevertLibrary)
        wx.EVT_MENU(self, ID_PPREFS, self.Prefs)
        wx.EVT_MENU(self, ID_QUIT, self.QuitLoopAnalyst)

        ##########
        # Event handlers for "editmenu"
        wx.EVT_MENU(self, ID_CUTCM, self.CutCM)
        wx.EVT_MENU(self, ID_COPYCM, self.CopyCM)
        wx.EVT_MENU(self, ID_PASTECM, self.PasteCM)
        wx.EVT_MENU(self, ID_DELCM, self.DeleteCM)
        wx.EVT_MENU(self, ID_DUPECM, self.DuplicateCM)
        wx.EVT_MENU(self, ID_EDITCM, self.EditCM)

        ##########
        # Event handlers for "analmenu"
        wx.EVT_MENU(self, ID_CLIPCM, self.ClipCommunityMatrix)
        wx.EVT_MENU(self, ID_CLIPGR, self.ClipGraph)
        wx.EVT_MENU(self, ID_CLIPPR, self.ClipPredictions)
        wx.EVT_MENU(self, ID_CLIPAT, self.ClipAdjoint)
        wx.EVT_MENU(self, ID_CLIPWF, self.ClipWFM)
        wx.EVT_MENU(self, ID_CLIPWP, self.ClipWPM)
        wx.EVT_MENU(self, ID_CLIPLE, self.ClipCLEM)
        wx.EVT_MENU(self, ID_CLIPAN, self.ClipAll)
        wx.EVT_MENU(self, ID_CLIPCO, self.ClipCorrelations)
        wx.EVT_MENU(self, ID_CLIPPA, self.ClipPaths)
        wx.EVT_MENU(self, ID_CLIPLP, self.ClipLoops)

        ##########
        # Event handlers for "helpmenu"
        wx.EVT_MENU(self, ID_ABOUT, self.About)
        wx.EVT_MENU(self, ID_HELP, self.Help)

        self.Show()


    ############################################################################
    ### AppUI EVENT HANDLERS                                                 ###
    ############################################################################

    ##########
    # HANDLER: ListBox Single Click
    def EvtListBox(self, event):
        self.UpdateDisplay()        

    ##########
    # HANDLER: Listbox Double Click
    def EvtListBoxDClick(self, event):
        self.EditCM()

    ##########
    # HANDLER: Notebook Change Tab
#    def Refocus(self, evt=None):
#        wx.CallAfter(self.SetFocus)

    ##########
    # HANDLER: Notebook advance to next tab, and library advance to next model
    def OnChar(self, event):
        self.Notebook.GetChildren()[3].SetFocus()   #Set the focus to the AuiTabCtrl child of the AuiNotebook instance
        count = self.ListBox.GetCount()
        key = event.GetKeyCode()
        if count > 1:
            index = int(self.ListBox.GetSelection())
            if key == wx.WXK_UP and self.ListBox.HasFocus() == False:
                if index > 0:
                    self.ListBox.SetSelection(index-1)
                elif index == 0:
                    self.ListBox.SetSelection(index)  # If at the top (front) of the ListBox, wrap around the the bottom (end).
            elif key == wx.WXK_DOWN and self.ListBox.HasFocus() == False:
                if index + 1 < count:
                    self.ListBox.SetSelection(index+1)
                elif index + 1 == count:    # If at the bottom (end) of the ListBox, wrap around the the top (front).
                    self.ListBox.SetSelection(index)
        self.UpdateDisplay()
        event.Skip()


    ##########
    # UpdateDisplay redraws the CMData on the CMDisplay using the current
    # selection from the ListBox
    def UpdateDisplay(self):
        self.Layout()
        self.SetTitle("Loop Analyst: "+GLOBAL.LibraryName)

        # Rebuild the graph(s) and analyses
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            if GLOBAL.Library.PrefsGraph == True:
                GLOBAL.Library.MakeGraph()
            GLOBAL.Library.MakeLoops()
            if GLOBAL.Library.PrefsCEM == True:
                GLOBAL.Library.MakeCEM()
                GLOBAL.Library.MakeCorrelations()
            if GLOBAL.Library.PrefsAdjoint == True:
                GLOBAL.Library.MakeAdjoint()
            if GLOBAL.Library.PrefsT == True:
                GLOBAL.Library.MakeT()
            if GLOBAL.Library.PrefsWFM == True:
                GLOBAL.Library.MakeWFM()
            if GLOBAL.Library.PrefsWPM == True:
                GLOBAL.Library.MakeWPM()
            if GLOBAL.Library.PrefsCLEM == True:
                GLOBAL.Library.MakeCLEM()

        if self.ListBox.GetCount() > 0:
            index = int(self.ListBox.GetSelection())
        else:
            index = 0

        GraphWidth = self.Page2.GetClientSize()[0]
        GraphHeight = self.Page2.GetClientSize()[1]

        ##########
        # Set the font for the tabbed display
        CMDisplayFont = wx.Font(GLOBAL.DisplayFontSize, wx.MODERN, wx.NORMAL, wx.BOLD)

        ##########
        # Update the Community Matrix tab's display
        self.Page1.DestroyChildren()
        self.PageCM = wx.StaticText(self.Page1, wx.NewId(), self.ReviseCMText(), style=wx.TE_MULTILINE)
        self.PageCM.SetFont(CMDisplayFont)

        ##########
        # Update the Graph tab's display
        self.Page2.DestroyChildren() # clear the display

        if GLOBAL.Library.PrefsGraph == True:
            if len(GLOBAL.Library.CommunityMatrices) > 0:
            
                # Read the CM.Graphed png data into an StringIO, then read an image from 
                # that data stream.
                GraphImageStream = StringIO(GLOBAL.Library.CommunityMatrices[index].Graphed)
                GraphImage = wx.ImageFromStream(GraphImageStream, wx.BITMAP_TYPE_ANY)

                # Scale the graph as needed.
                scale_factor = 1
                if GraphWidth > GraphHeight:
                    NewHeight = int(round((float(GraphHeight * scale_factor)/float(GraphImage.GetWidth())) * float(GraphImage.GetHeight())))
                    NewWidth = int(round((float(GraphHeight * scale_factor)/float(GraphImage.GetWidth())) * float(GraphImage.GetWidth())))
                else:
                    NewHeight = int(round((float(GraphWidth * scale_factor)/float(GraphImage.GetWidth())) * float(GraphImage.GetHeight())))
                    NewWidth = int(round((float(GraphWidth * scale_factor)/float(GraphImage.GetWidth())) * float(GraphImage.GetWidth())))
                GraphImage = GraphImage.Scale(NewWidth,NewHeight)

                # display the graph image as a static bitmap
                DisplayedGraph = wx.StaticBitmap(self.Page2, wx.NewId(), wx.BitmapFromImage(GraphImage)).Center()

        ##########
        # Update the Community Effect Matrix tab's display
        self.Page3.DestroyChildren()
        self.PageCEM = wx.StaticText(self.Page3, wx.NewId(), self.ReviseCEMText(), style=wx.TE_MULTILINE)
        self.PageCEM.SetFont(CMDisplayFont)

        ##########
        # Update the Adjoint and T Matrices tab's display
        self.Page4.DestroyChildren()
        self.PageAdjoint = wx.StaticText(self.Page4, wx.NewId(), self.ReviseAdjointText(), style=wx.TE_MULTILINE)
        self.PageAdjoint.SetFont(CMDisplayFont)

        ##########
        # Update the Weighted Feedback Matrix tab's display
        self.Page5.DestroyChildren()
        self.PageWFM = wx.StaticText(self.Page5, wx.NewId(), self.ReviseWFMText(), style=wx.TE_MULTILINE)
        self.PageWFM.SetFont(CMDisplayFont)

        ##########
        # Update the Weighted Prediction Matrix tab's display
        self.Page6.DestroyChildren()
        self.PageWPM = wx.StaticText(self.Page6, wx.NewId(), self.ReviseWPMText(), style=wx.TE_MULTILINE)
        self.PageWPM.SetFont(CMDisplayFont)

        ##########
        # Update the Change in Life Expectancy Matrix tab's display
        self.Page7.DestroyChildren()
        self.PageCLE = wx.StaticText(self.Page7, wx.NewId(), self.ReviseCLEMText(), style=wx.TE_MULTILINE)
        self.PageCLE.SetFont(CMDisplayFont)

        ##########
        # Update other stuff
        self.MenuBar.UpdateMenus()
        self.Refresh(eraseBackground=True)
        
    ##########
    # FUNCTION: Undo
    # Undo replaces the working library with the previous one in the history
    def Undo(self, Event = None):
        if GLOBAL.HistoryIndex > 0:
            # Decrement the HistoryIndex
            GLOBAL.HistoryIndex = GLOBAL.HistoryIndex - 1
            GLOBAL.Library = GLOBAL.History[GLOBAL.HistoryIndex]

            # Set the current library name and names
            GLOBAL.LibraryName = GLOBAL.History[GLOBAL.HistoryIndex].Name
            GLOBAL.Library.names = GLOBAL.History[GLOBAL.HistoryIndex].names

            # Clear listbox
            self.ListBox.Clear()

            # Update the library
            for x in GLOBAL.Library.CommunityMatrices:
                # Add the name to the listbox
                self.AddNewCM(x.name)
### replace the blow line to try and keep the selection in the same place before 
### or after undo/redo
            self.ListBox.SetSelection(0, select = True)
#            self.ListBox.SetSelection(self.ListBox.GetCount(), select = True)

        # Display the indexed CMLibrary
        self.SetTitle("Loop Analyst: "+GLOBAL.LibraryName)
        self.UpdateDisplay()

    ##########
    # FUNCTION: Redo
    # Redo replaces the working library with the subsequent one in the history
    def Redo(self, Event = None):
        if GLOBAL.HistoryIndex < len(GLOBAL.History) - 1:
            GLOBAL.HistoryIndex = GLOBAL.HistoryIndex + 1
            GLOBAL.Library = GLOBAL.History[GLOBAL.HistoryIndex]

            # Set the current library name and names
            GLOBAL.LibraryName = GLOBAL.History[GLOBAL.HistoryIndex].Name
            GLOBAL.Library.names = GLOBAL.History[GLOBAL.HistoryIndex].names

            # Clear listbox
            self.ListBox.Clear()

            # Update the library
            for x in GLOBAL.Library.CommunityMatrices:
                # Add the name to the listbox
                self.AddNewCM(x.name)
### replace the blow line to try and keep the selection in the same place before 
### or after undo/redo
            self.ListBox.SetSelection(0, select = True)
#            self.ListBox.SetSelection(self.ListBox.GetCount(), select = True)

        # Display the indexed CMLibrary
        self.SetTitle("Loop Analyst: "+GLOBAL.LibraryName)
        self.UpdateDisplay()

    ##########
    # FUNCTION: AddNewCM 
    # AddNewCM adds the name of a New CM to the ListBox
    def AddNewCM(self,NAME):
        END = self.ListBox.GetCount()
        # Add the supplied NAME to the ListBox
        self.ListBox.Insert(NAME, END)
        # Deselect all items
        for item in range(0,END):
            self.ListBox.SetSelection(item,select=False)
        # Set the last item to be selected
        self.ListBox.SetSelection(END)
        # Insure that last item is visible
#        self.ListBox.SetFirstItem(END)
        
    ##########
    # FUNCTION: NewCM creates a new community matrix and displays it in self.ListBox 
    def NewCM(self, Event=None):
        NCMdlg = NewCMDialog(self, -1, GLOBAL.language["dialog_NewCMDialog"][0], size=(350, 200),
                         style=wx.DEFAULT_DIALOG_STYLE
                         )
        NCMdlg.CenterOnScreen()

        NCMdlg.Bind(wx.EVT_CHAR_HOOK, None)
        # NCMdlg does not return until the dialog is closed.
        
        ##########
        # Handler for NCMdlg
        Value = NCMdlg.ShowModal()

        if Value == wx.ID_OK:

            ##########
            # Check upon presence of DATA
            
            # Show an alert if the DATA values are not present, and cancel the handler
            if NCMdlg.DATA.GetValue() == "":
                alert = wx.MessageDialog( self, GLOBAL.language["dialog_NewCMDataAlert"][0][0],GLOBAL.language["dialog_NewCMDataAlert"][0][1], wx.OK)
                alert.ShowModal() # Shows it
                alert.Bind(wx.EVT_CHAR_HOOK, None)
                NCMdlg.Destroy()
                return

            ##########
            # Check upon presence of NAME and the duplicity of NAME in the library, 
            # modify as appropriate...
            
            # If NCMdlg.NAME.GetValue() is empty and unchanged replace it locally 
            # with "Matrix"...
            NAME = NCMdlg.NAME.GetValue()
            if NAME == "":
                NAME = GLOBAL.language["dialog_NewCMName"][0]

            # Otherwise, if NCMdlg.NAME.GetValue is not empty...
            # If there are ListBox elements and the NCMdlg.NAME.get() is not in 
            # GLOBAL.Library.names...
            if GLOBAL.Editindex != None:
                if self.ListBox.GetCount() > 0 and NAME in GLOBAL.Library.names[:GLOBAL.Editindex]+GLOBAL.Library.names[GLOBAL.Editindex+1:]:
                    # ...and then appropriately increment the name "Matrix" if it is a 
                    # duplicate. 
                    Count = 2
                    for x in GLOBAL.Library.names:
                        if NAME == x:
                            while NAME+str(Count) in GLOBAL.Library.names:
                                Count = Count + 1
                            NAME = NAME+" "+str(Count)
                # Else if there are ListBox elements and the NCMdlg.NAME.get() _is_ in
                # GLOBAL.Library.names, we just let the assignment of NAME to 
                # NCMdlg.NAME.GetValue() stand.                

            if GLOBAL.Editindex == None:
                if self.ListBox.GetCount() > 0 and NAME in GLOBAL.Library.names:
                    # ...and then appropriately increment the name "Matrix" if it is a 
                    # duplicate. 
                    Count = 2
                    for x in GLOBAL.Library.names:
                        if NAME == x:
                            while NAME+str(Count) in GLOBAL.Library.names:
                                Count = Count + 1
                            NAME = NAME+" "+str(Count)
                # Else if there are ListBox elements and the NCMdlg.NAME.get() _is_ in
                # GLOBAL.Library.names, we just let the assignment to NAME to 
                # NCMdlg.NAME.GetValue() stand.
        
            ##########
            # Use the NCMdlg value to create a new communty matrix, and display it...

            # Instantiate a new CommunityMatrix with the provided values as 
            # appropriate for the presence or absence of names
            DATA = NCMdlg.DATA.GetValue()
            NAMES = NCMdlg.NAMES.GetValue()
            if NAMES == "":
                CM = CommunityMatrix(eval(DATA),NAME)
            else:
                CM = CommunityMatrix(eval(DATA),NAME,eval(NAMES))            
            
            # if validate_cm returned false, then CM.A was set equal to []
            if CM.A != []:
                # if this is not an edit, then just add the new CM
                if GLOBAL.Editindex == None:
                    self.AddNewCM(NAME)
                    GLOBAL.Library.AddCM(CM)
                # else, if this is an edit, then delete the prior CM, and 
                # add the edited cm in its place. 
                else:
                    self.ListBox.Delete(GLOBAL.Editindex)
                    self.ListBox.Insert(NAME, GLOBAL.Editindex)
                    GLOBAL.Library.CommunityMatrices[GLOBAL.Editindex] = CM
                    GLOBAL.Library.names[GLOBAL.Editindex] = NAME
                    for item in range(0,self.ListBox.GetCount()):
                        self.ListBox.SetSelection(item, select = False)
                    self.ListBox.SetSelection(GLOBAL.Editindex, select = True)

### rewrite to make the below line happen only if the GetCount of the list 
### box is greater than the visible length of the listbox
#                self.ListBox.SetFirstItem(GLOBAL.Editindex)
            
            self.AddToHistory()
                        
            # Display the new CM
            self.UpdateDisplay()

        NCMdlg.Destroy()

    ##########
    # FUNCTION: NewLibrary discards the existing CMLibrary, initializes a new one, and
    # clears all entries of the ListBox.
    def NewLibrary(self, Event=None):
        
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            NewLibraryDialog = ConfirmDialog(self, -1, GLOBAL.language["dialog_NewLibraryConfirm"][0][0],GLOBAL.language["dialog_NewLibraryConfirm"][0][1], save=True)
            NewLibraryDialog.CenterOnScreen()
            NewLibraryDialog.Bind(wx.EVT_CHAR_HOOK, None)
            # NewLibraryDialog does not return until the dialog is closed.
        
            ##########
            # Handler for NewLibraryDialog
            Value = NewLibraryDialog.ShowModal()
            if Value == wx.ID_OK:
                GLOBAL.Library = CMLibrary()
                GLOBAL.LibraryName = GLOBAL.language["dialog_NewLibraryName"][0]
                GLOBAL.Cache = []
                self.ResetHistory()
                self.ListBox.Clear()
                self.UpdateDisplay()
            NewLibraryDialog.Destroy()

    ##########
    # FUNCTION: OpenRecentsX opens the relevant CMLibrary file
    def OpenRecents1(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (1):
            self.Open(GLOBAL.RecentLibraries[0])
    def OpenRecents2(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (2):
            self.Open(GLOBAL.RecentLibraries[1])
    def OpenRecents3(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (3):
            self.Open(GLOBAL.RecentLibraries[2])
    def OpenRecents4(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (4):
            self.Open(GLOBAL.RecentLibraries[3])
    def OpenRecents5(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (5):
            self.Open(GLOBAL.RecentLibraries[4])
    def OpenRecents6(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (6):
            self.Open(GLOBAL.RecentLibraries[5])
    def OpenRecents7(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (7):
            self.Open(GLOBAL.RecentLibraries[6])
    def OpenRecents8(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (8):
            self.Open(GLOBAL.RecentLibraries[7])
    def OpenRecents9(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (9):
            self.Open(GLOBAL.RecentLibraries[8])
    def OpenRecents10(self, Event=None):
        if len(GLOBAL.RecentLibraries) >= (10):
            self.Open(GLOBAL.RecentLibraries[9])

    ##########
    # FUNCTION: Open opens a CMLibrary file
    def Open(self, Path):
        """Make use of the supplied path to update GLOBAL.RecentDirectory, the history, and open the given file."""
        if GLOBAL.HistoryIndex > 0:
            NewLibraryDialog = ConfirmDialog(self, -1, GLOBAL.language["dialog_OpenConfirm"][0][0], GLOBAL.language["dialog_OpenConfirm"][0][1], save=True)
            NewLibraryDialog.CenterOnScreen()
            Value = NewLibraryDialog.ShowModal()
            if Value == wx.ID_CANCEL:
                return
        if exists(Path):
            FileName = self.ReturnFile(Path)
            GLOBAL.LibraryName = FileName[0:len(FileName)-4]  # Set the current library name
            GLOBAL.Library.Name = FileName[0:len(FileName)-4]
            GLOBAL.RecentDirectory = Path[0:len(Path)-len(FileName)]  # Set the GLOBAL.RecentDirectory
            self.AddRecentLibrary(Path)  # Add the path to the GLOBAL.RecentLibraries (this updates preferences)
            self.ListBox.Clear()  # Clear listbox
            FILE = file(Path,'r')  # Import library
            GLOBAL.Library = load(FILE)
            FILE.close()
            GLOBAL.LibraryLastSaved = deepcopy(GLOBAL.Library)
            GLOBAL.Library.names = []
            for x in GLOBAL.Library.CommunityMatrices:
                self.AddNewCM(x.name)  # Add the name to the listbox
                GLOBAL.Library.names = GLOBAL.Library.names+[x.name]  # Reconstruct the Library.names
            self.ListBox.SetSelection(0, select = True)
            self.SetTitle("Loop Analyst: "+GLOBAL.LibraryName)  # Display the new CM
            self.ResetHistory()
            self.Menubar()
            self.UpdateDisplay()


    ##########
    # FUNCTION: RecentMenuEntries takes a list of file paths and returns a list of
    # CML file names with any necessarily high path qualifications to differentiate
    # files with the same name
    def RecentMenuEntries(self, RecentPaths):
        Entries = []    #Initialize the list of names to be returned
        for i in RecentPaths: #Start by adding CML files names
            if '/' in i:    #Include only the file name in the deepest directory
                Entries = Entries + [i.split("/")[-1]]
            else:           #The special case of a file residing at the root directory
                Entries = Entries + [i]
        #Check for duplicate file names, and differentiate by path
        Entries = self.CheckDuplicateEntries(Entries, RecentPaths)
        return Entries

    ##########
    # FUNCTION: CheckDuplicateEntries is used by RecentMenuEntries to clarify files
    # sharing the same name by appending portions of their paths
    def CheckDuplicateEntries(self, list, paths):
        N = len(list)
        for i in range(0,(N-1)):
            if self.ExactIn(list[i],list[i+1:N]):
                for j in self.IndexDuplicates(list[i],list[i+1:N],i):
                    if "/" in paths[j]:
                        list[j] = paths[j].split("/")[-2 - list[j].count("/")] + "/" + list[j]
                    else:
                        list[j] = "/" + list[j]
        for i in range(0,N):
            if ("/" in list[i]) and list[i][0] != "/":
                list[i] = "/"+str(list[i])
        return list

    ##########
    # FUNCTION: IndexDuplicates is used by Check DuplicateEntries to return a list
    # of indices for duplicated names
    def IndexDuplicates(self,s,list,offset):
        N = len(list)
        Indices = []
        for i in range(0,N):
            if s in list[i]:
                Indices = Indices + [i+offset+1]
        Indices = [offset] + Indices
        return Indices

    ##########
    # FUNCTION: ExactIn tests exact equality of string s within a list and returns
    # true on a match with any list element, an false otherwise
    def ExactIn(self,s,list):
        for i in list:
            if s == i:
                return True
        return False

    ##########
    # FUNCTION: OpenLibraryDialog solicits a path and file, confirms it as a .cml file,  
    # then reinitializes the GLOBAL.Library with it, and repopulates the ListBox.
    def OpenLibraryDialog(self, Event=None):

        if GLOBAL.RecentDirectory == "":
            WorkingDirectory = getcwd()
        else:
            WorkingDirectory = GLOBAL.RecentDirectory

        ##########
        # The OLdlg interface
        OLdlg = wx.FileDialog(
            self,
            message = GLOBAL.language["dialog_OpenLibraryMessage"][0],
            defaultDir = WorkingDirectory,
            defaultFile = "",
            wildcard = GLOBAL.language["dialog_OpenLibraryWildcard"][0],
            style=wx.OPEN | wx.CHANGE_DIR
            )

        if OLdlg.ShowModal() == wx.ID_OK:
            OLdlg.Bind(wx.EVT_CHAR_HOOK, None)
            OLfile = OLdlg.GetPaths()
            self.Open(OLfile[0])
        OLdlg.Destroy()

    ##########
    # FUNCTION: ClearRecents clears GLOBAL.RecentLibraries
    def ClearRecents(self, Event=None):
        GLOBAL.RecentLibraries = []
        self.Menubar()

    ##########
    # FUNCTION: AppendLibraryDialog solicits a path and file, confirms it as a .cml file,  
    # then appends its data to the GLOBAL.Library, and repopulates the ListBox.
    def AppendLibraryDialog(self, Event=None):

        if GLOBAL.RecentDirectory == "":
            WorkingDirectory = getcwd()
        else:
            WorkingDirectory = GLOBAL.RecentDirectory

        ##########
        # The ALdlg interface
        ALdlg = wx.FileDialog(
            self,
            message = GLOBAL.language["dialog_AppendLibraryMessage"][0],
            defaultDir = WorkingDirectory,
            defaultFile = "",
            wildcard = GLOBAL.language["dialog_AppendLibraryWildcard"][0],
            style=wx.OPEN | wx.CHANGE_DIR
            )

        if ALdlg.ShowModal() == wx.ID_OK:
            ALdlg.Bind(wx.EVT_CHAR_HOOK, None)
            ALfile = ALdlg.GetPaths()
            FileName = self.ReturnFile(ALfile[0])

            # Import Library
            FILE = file(ALfile[0],'r')
            AppendLibrary = load(FILE)
            FILE.close()
            GLOBAL.Library.names = GLOBAL.Library.names + AppendLibrary.names
            GLOBAL.Library.CommunityMatrices = GLOBAL.Library.CommunityMatrices + AppendLibrary.CommunityMatrices
            for x in AppendLibrary.CommunityMatrices:
                # Add the name to the listbox
                self.AddNewCM(x.name)
            
            # Display the new CM
            self.AddToHistory()
            self.UpdateDisplay()
            
        ALdlg.Destroy()

    ##########
    # FUNCTION: SaveLibrary
    def SaveLibrary(self, Event = None):
        # Check CMLibrary.Name, and, if it is "Untitled" Save As.
        if GLOBAL.LibraryName == GLOBAL.language["dialog_SaveLibrary"][0] or GLOBAL.LibraryName == "":
            self.SaveAsLibraryDialog()
            return
        else:
        # Pickle the Library.
            SaveName = GLOBAL.RecentLibraries[0]
            if lower(SaveName[-4:]) != ".cml":
                SaveName = SaveName+".cml"
            LibraryFile = file(SaveName,"w")
            dump(GLOBAL.Library, LibraryFile, 1)
            LibraryFile.close()
            self.ResetHistory()
            GLOBAL.LibraryLastSaved = deepcopy(GLOBAL.Library)

    ##########
    # FUNCTION: SaveAsLibraryDialog opens a dialog with which to save the current library.
    def SaveAsLibraryDialog(self, Event=None):

        if GLOBAL.RecentDirectory == "":
            WorkingDirectory = getcwd()
        else:
            WorkingDirectory = GLOBAL.RecentDirectory

        if GLOBAL.LibraryName == "":
            DefaultName = GLOBAL.language["dialog_SaveAsLibraryDefaultName"][0]
        else:
            DefaultName = GLOBAL.LibraryName

        SALdlg = wx.FileDialog(
            self, 
            message=GLOBAL.language["dialog_SaveAsLibraryMessage"][0],
            defaultDir=WorkingDirectory, 
            defaultFile=DefaultName, 
            wildcard=GLOBAL.language["dialog_SaveAsLibraryWildcard"][0],
            style=wx.SAVE
            )

        if SALdlg.ShowModal() == wx.ID_OK:
            SALdlg.Bind(wx.EVT_CHAR_HOOK, None)
            SaveName = SALdlg.GetPath()
            if lower(SaveName[-4:]) != ".cml":
                SaveName = SaveName+".cml"

            # Set the GLOBAL.RecentDirectory
            GLOBAL.RecentDirectory = SaveName[0:-(len(self.ReturnFile(SaveName))+1)]
            
            GLOBAL.LibraryName = self.ReturnFile(SaveName)[0:-4]
            self.SetTitle("Loop Analyst: "+GLOBAL.LibraryName)
            LibraryFile = file(SaveName,"w")
            dump(GLOBAL.Library, LibraryFile, 1)
            LibraryFile.close()
            GLOBAL.LibraryLastSaved = deepcopy(GLOBAL.Library)
            self.AddRecentLibrary(SaveName)

            # Update the preferences
            self.UpdatePreferences()

        SALdlg.Destroy()
    
    ##########
    # FUNCTION: SaveGraph
    # Saves a copy of the currently selected system's graph.
    def SaveGraph(self, Event = None):
        if GLOBAL.Library.PrefsGraph == True and self.ListBox.GetCount() > 0:
            # Get the reference position
            index = int(self.ListBox.GetSelection())

            # Define a working directory
            if GLOBAL.RecentDirectory == "":
                WorkingDirectory = getcwd()
            else:
                WorkingDirectory = GLOBAL.RecentDirectory

            # Save the graph png file from CM.Graph
            SaveDialog = wx.FileDialog(
            self, 
            message=GLOBAL.language["dialog_SaveGraphMessage"][0],
            defaultDir=WorkingDirectory, 
            defaultFile=str(GLOBAL.Library.CommunityMatrices[index].name)+".dot", 
            wildcard=GLOBAL.language["dialog_SaveGraphWildcard"][0],
            style=wx.SAVE
            )

            if SaveDialog.ShowModal() == wx.ID_OK:
                SaveDialog.Bind(wx.EVT_CHAR_HOOK, None)
                ExportName = SaveDialog.GetPath()
                if lower(ExportName[-4:]) != ".png":
                    ExportName = ExportName+".png"
                ExportFile = file(ExportName, "wb")
                ExportFile.writelines(str(GLOBAL.Library.CommunityMatrices[index].Graphed))
                ExportFile.close()

            SaveDialog.Destroy()
        
    ##########
    # FUNCTION: ImportCMDialog solicits a path and file, confirms it as a .txt file,  
    # then appends its data to the GLOBAL.Library, and repopulates the ListBox.
    def ImportCMDialog(self, Event=None):

        if GLOBAL.RecentDirectory == "":
            WorkingDirectory = getcwd()
        else:
            WorkingDirectory = GLOBAL.RecentDirectory

        ##########
        # The ImportCMdlg interface
        ImportCMdlg = wx.FileDialog(
            self,
            message = GLOBAL.language["dialog_ImportCMMessage"][0],
            defaultDir = WorkingDirectory,
            defaultFile = "",
            wildcard = GLOBAL.language["dialog_ImportCMWildcard"][0],
            style=wx.OPEN | wx.CHANGE_DIR
            )

        if ImportCMdlg.ShowModal() == wx.ID_OK:
            ImportCMdlg.Bind(wx.EVT_CHAR_HOOK, None)
            ImportFile = ImportCMdlg.GetPaths()
            FileName = str(ImportFile)[3:-2]

            # Import CMs
            Import = open(FileName)
	    print "imported \n"
            try:
                count = 0
                for line in Import:
                    count = count + 1
                    line = line.rstrip()
                    cm = self.ParseLA1(line)
                    if (cm == False):
                        cm = self.ParseMaple(line)
                    if (cm == False):
                        cm = self.ParseR(line)
                    if (cm == False):
                        alert = wx.MessageDialog(frame, GLOBAL.language["dialog_ImportCMAlert"][0][0],str(count),GLOBAL.language["dialog_ImportCMAlert"][0][1], wx.OK)
                        alert.ShowModal() # Shows it
                        alert.Bind(wx.EVT_CHAR_HOOK, None)
                    if (cm != False):

                        # If Name is empty replace it locally 
                        # with "Matrix"...
                        NAME = cm[2]
                        if NAME == "":
                            NAME = GLOBAL.language["dialog_ImportCMName"][0]

                        # Otherwise, if Name is not empty...
                        # If there are ListBox elements and Name is not in 
                        # GLOBAL.Library.names...
                        if GLOBAL.Editindex != None:
                            if self.ListBox.GetCount() > 0 and NAME in GLOBAL.Library.names[:GLOBAL.Editindex]+GLOBAL.Library.names[GLOBAL.Editindex+1:]:
                                # ...and then appropriately increment the name "Matrix" if it is a 
                                # duplicate. 
                                Count = 2
                                for x in GLOBAL.Library.names:
                                    if NAME == x:
                                        while NAME+str(Count) in GLOBAL.Library.names:
                                            Count = Count + 1
                                        NAME = NAME+" "+str(Count)
                            # Else if there are ListBox elements and Name _is_ in
                            # GLOBAL.Library.names, we just let the assignment of NAME to 
                            # Name stand.                

                        if GLOBAL.Editindex == None:
                            if self.ListBox.GetCount() > 0 and NAME in GLOBAL.Library.names:
                                # ...and then appropriately increment the name "Matrix" if it is a 
                                # duplicate. 
                                Count = 2
                                for x in GLOBAL.Library.names:
                                    if NAME == x:
                                        while NAME+str(Count) in GLOBAL.Library.names:
                                            Count = Count + 1
                                        NAME = NAME+" "+str(Count)
                            # Else if there are ListBox elements and the Name _is_ in
                            # GLOBAL.Library.names, we just let the assignment to NAME to 
                            # Name stand.
                    
                        ##########
                        # Use the cm value to create a new communty matrix, and display it...

                        # Instantiate a new CommunityMatrix with the provided values as 
                        # appropriate for the presence or absence of names
                        DATA = cm[0]
                        NAMES = cm[1]
                        if NAMES == "":
                            CM = CommunityMatrix(eval(DATA),NAME)
                        else:
                            CM = CommunityMatrix(eval(DATA),NAME,eval(NAMES))            
                        
                        # if validate_cm returned false, then CM.A was set equal to []
                        if CM.A != []:
                            self.AddNewCM(NAME)
                            GLOBAL.Library.AddCM(CM)

            ### rewrite to make the below line happen only if the GetCount of the list 
            ### box is greater than the visible length of the listbox
            #                self.ListBox.SetFirstItem(GLOBAL.Editindex)
                        
                        self.AddToHistory()
                        # Display the importd CM
                        self.UpdateDisplay()
            finally:
                Import.close()
    
        ImportCMdlg.Destroy()

    ##########
    # FUNCTION: ExportAnalysis
    def ExportAnalysis(self, Event = None):

        if len(GLOBAL.Library.CommunityMatrices) > 0:
            # Get the reference position
            index = deepcopy(int(self.ListBox.GetSelection()))

            # Define a working directory
            if GLOBAL.RecentDirectory == "":
                WorkingDirectory = getcwd()
            else:
                WorkingDirectory = GLOBAL.RecentDirectory

            # Export the file from CM.CEM
            FileName = str(GLOBAL.Library.CommunityMatrices[index].name)
            EXAnalysisdlg = wx.FileDialog(
                self,
                message=GLOBAL.language["dialog_ExportAnalysisMessage"][0],
                defaultDir=WorkingDirectory,
                defaultFile=FileName,
                wildcard=GLOBAL.language["dialog_ExportAnalysisWildcard"][0],
                style=wx.SAVE)

            if EXAnalysisdlg.ShowModal() == wx.ID_OK:
                EXAnalysisdlg.Bind(wx.EVT_CHAR_HOOK, None)
                ExportName = EXAnalysisdlg.GetPath()
                ExportFile = file(ExportName, "w")
                ExportFile.writelines(self.ReviseCMText())
                ExportFile.writelines(self.ReviseCEMText())
                ExportFile.writelines(self.ReviseAdjointText())
                ExportFile.writelines(self.ReviseWFMText())
                ExportFile.writelines(self.ReviseWPMText())
                ExportFile.writelines(self.ReviseCLEMText())
                ExportFile.close()

            EXAnalysisdlg.Destroy()

    ##########
    # FUNCTION: ExportGraph
    def ExportGraph(self, Event = None):
        if GLOBAL.Library.PrefsGraph == True and len(GLOBAL.Library.CommunityMatrices) > 0:

            # Get the reference position
            index = int(self.ListBox.GetSelection())

            # Define a working directory
            if GLOBAL.RecentDirectory == "":
                WorkingDirectory = getcwd()
            else:
                WorkingDirectory = GLOBAL.RecentDirectory

            # Export the dot file from CM.Graph
            ExportGraphDialog = wx.FileDialog(
            self, 
            message=GLOBAL.language["dialog_ExportGraphMessage"][0],
            defaultDir=WorkingDirectory, 
            defaultFile=str(GLOBAL.Library.CommunityMatrices[index].name)+".dot", 
            wildcard=GLOBAL.language["dialog_ExportGraphWildcard"][0],
            style=wx.SAVE
            )

            if ExportGraphDialog.ShowModal() == wx.ID_OK:
                ExportGraphDialog.Bind(wx.EVT_CHAR_HOOK, None)
                ExportName = ExportGraphDialog.GetPath()
                if lower(ExportName[-4:]) != ".dot":
                    ExportName = ExportName+".dot"
                ExportFile = file(ExportName, "w")
                ExportFile.writelines(str(GLOBAL.Library.CommunityMatrices[index].Graph))
                ExportFile.close()

            ExportGraphDialog.Destroy()

    ##########
    # FUNCTION: RevertLibrary
    # Reverts to last saved version of GLOBAL.Library
    def RevertLibrary(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            self.ListBox.Clear()
            GLOBAL.Library.names = []
            for x in GLOBAL.LibraryLastSaved.CommunityMatrices:
                # Add the name to the listbox
                self.AddNewCM(x.name)
                # Reconstruct the Library.names
                GLOBAL.Library.names = GLOBAL.LibraryLastSaved.names+[x.name]
                GLOBAL.Library = deepcopy(GLOBAL.LibraryLastSaved)
                self.ResetHistory()

                # Display the new CM
                self.UpdateDisplay()
        
    ##########
    # FUNCTION: Preferences
    # Opens the preferences dialog
    def Prefs(self, Event = None):
        PrefsDialog = PreferencesDialog(self, -1, GLOBAL.language["dialog_PreferencesDialog"][0], size=(640, 480), style=wx.DEFAULT_DIALOG_STYLE)
        PrefsDialog.CenterOnScreen()
        PrefsDialog.Bind(wx.EVT_CHAR_HOOK, None)
        
        ##########
        # Handler for Prefsdlg

        # Prefsdlg does not return until the dialog is closed.
        Value = PrefsDialog.ShowModal()

        if Value == wx.ID_OK:

            matrices = self.ListBox.GetCount()  # prepare to reset flags for current CM if needed

            # Graphs in color, grayscale or B&W...
            if GLOBAL.GraphColoring != PrefsDialog.ColorSchemeRadiobox.GetSelection():
                GLOBAL.GraphColoring = PrefsDialog.ColorSchemeRadiobox.GetSelection()
                for matrix in range(0,matrices):
                    GLOBAL.Library.CommunityMatrices[matrix].GraphFlag = False
                self.UpdateDisplay()

            # Internationalize langauge if needed...
            if GLOBAL.Language != PrefsDialog.LanguageRadiobox.GetSelection():
                GLOBAL.Language = PrefsDialog.LanguageRadiobox.GetSelection()
  
                # Get path to Loop Analyst.py
                LApath = split(realpath(__file__))[0]

                # Set the language internationalization
                if GLOBAL.Language == 0:
                    if exists(LApath+'/localizations/en-us.localization'):
                        GLOBAL.language = load(file(LApath+'/localizations/en-us.localization',"r"))
                if GLOBAL.Language == 1:
                    if exists(LApath+'/localizations/en-uk.localization'):
                        GLOBAL.language = load(file(LApath+'/localizations/en-uk.localization',"r"))
                self.Menubar()
                self.UILayout()


### YOU NEED TO VALIDATE THE PATH IN SOME WAY HERE!                
            if GLOBAL.dotLocation != PrefsDialog.dotpath.GetValue():
                GLOBAL.dotLocation = PrefsDialog.dotpath.GetValue()
                for matrix in range(0,matrices):
                    GLOBAL.Library.CommunityMatrices[matrix].GraphFlag = False
                GLOBAL.Library.MakeGraph()

            GLOBAL.DisplayFontSize = int(PrefsDialog.displayfontsize.GetValue())

            if GLOBAL.WeightedPredictionThreshold != float(PrefsDialog.weightedpredictionthreshold.GetValue()) or GLOBAL.ThresholdCriterion != PrefsDialog.ThresholdRadiobox.GetSelection():
                if isinstance(float(PrefsDialog.weightedpredictionthreshold.GetValue()), float) and float(PrefsDialog.weightedpredictionthreshold.GetValue()) > 0.0 and float(PrefsDialog.weightedpredictionthreshold.GetValue()) <= 1.0:
                    GLOBAL.WeightedPredictionThreshold = float(PrefsDialog.weightedpredictionthreshold.GetValue())
                if PrefsDialog.ThresholdRadiobox.GetSelection() == 0:
                    GLOBAL.ThresholdCriterion = 0
                else:
                    GLOBAL.ThresholdCriterion = 1
                for matrix in range(0,matrices):
                    GLOBAL.Library.CommunityMatrices[matrix].WPMFlag = False
                GLOBAL.Library.MakeWPM()

            if GLOBAL.WeightedFeedbackPrecision != int(PrefsDialog.weightedfeedbackprecision.GetValue()):
                if isinstance(int(PrefsDialog.weightedfeedbackprecision.GetValue()), int) and int(PrefsDialog.weightedfeedbackprecision.GetValue()) > 0 and int(PrefsDialog.weightedfeedbackprecision.GetValue()) < 9:
                    GLOBAL.WeightedFeedbackPrecision = int(PrefsDialog.weightedfeedbackprecision.GetValue())
                    for matrix in range(0,matrices):
                        GLOBAL.Library.CommunityMatrices[matrix].WFMFlag = False
                        GLOBAL.Library.CommunityMatrices[matrix].WPMFlag = False
                    GLOBAL.Library.MakeWFM()
                    GLOBAL.Library.MakeWPM()
                        
            self.UpdatePreferences()
            self.UpdateDisplay()

        PrefsDialog.Destroy()
                
    ##########
    # QuitLoopAnalyst
    def QuitLoopAnalyst(self, Event = None):
        self.Close(True)  # Close the frame.
        self.UpdatePreferences()
        raise SystemExit
    
    ##########
    # FUNCTION: CutCM
    # CutCM copies the selected community matrix to GLOBAL.CMDataClip
    # and the name to CMNameClip and removes the entry from self.ListBox
    # and the GLOBAL.Library.CommunityMatricies
    def CutCM(self, Event=None):
        self.CopyCM()
        self.DeleteCM()

    ##########
    # FUNCTION: CopyCM 
    # CopyCM copies the selected community matrix to GLOBAL.CMDataClip
    # and the name to CMNameClip
    def CopyCM(self, Event=None):
        index = self.ListBox.GetSelection()
        if index > 0:
            GLOBAL.CMDataClip = deepcopy(GLOBAL.Library.CommunityMatrices[index])
            GLOBAL.CMNameClip = GLOBAL.CMDataClip.name

    ##########
    # FUNCTION: PasteCM 
    # PasteCM makes a duplicate of the selected Community matrix and adds it 
    # to the ListBox.
    def PasteCM(self, Event=None):

        # if the ListBox is not empty...
        if self.ListBox.GetCount() > 0:

            # Get the reference position
            index = int(self.ListBox.GetSelection())

            # Split the list into parts in front of and in back of the copy's 
            # insertion point.
            front = GLOBAL.Library.names[:index+1]
            back = GLOBAL.Library.names[index+1:]

            # Do the same for the list of community matrices in the library
            CMfront = GLOBAL.Library.CommunityMatrices[:index+1]
            CMback = GLOBAL.Library.CommunityMatrices[index+1:]
            
            # Produce an appropriate and unique name
            Alternate = GLOBAL.CMNameClip
            for x in GLOBAL.Library.names:
                if Alternate == x:
                    while Alternate in GLOBAL.Library.names:
                        Alternate = Alternate+GLOBAL.language["dialog_PasteCMName"][0]

            # Insert the entry into the list box, shift selection and update the display
            self.ListBox.Insert(Alternate, index+1)
            for item in range(0,self.ListBox.GetCount()):
                self.ListBox.SetSelection(item, select = False)
            self.ListBox.SetSelection(index+1)

            # Insert the copied data into the Library
            GLOBAL.Library.CommunityMatrices = CMfront+[GLOBAL.CMDataClip]+CMback
            
            # Remake the Library names
            GLOBAL.Library.MakeNames()
            self.AddToHistory()
            self.UpdateDisplay()

    ##########
    # FUNCTION: DeleteCM 
    # DeleteCM deletes a CommunityMatrix and its name from the ListBox
    # ADD A CONFIRM ON PREFERENCE CHECK!
    def DeleteCM(self, Event=None):

        # if the ListBox is not empty...
        END = self.ListBox.GetCount()
        if END > 0:
            GLOBAL.Library.DeleteCM(self.ListBox.GetStringSelection())
            GLOBAL.Library.MakeNames()
            self.ListBox.Delete(self.ListBox.GetSelection())
            for item in range(0,(END-1)):
                self.ListBox.SetSelection(item, select = False)
            self.ListBox.SetSelection(END-2, select = True)
            self.AddToHistory()
            self.UpdateDisplay()

    ##########
    # FUNCTION: DuplicateCM 
    # DuplicateCM makes a duplicate of the selected Community matrix and adds it 
    # to the ListBox.
    def DuplicateCM(self, Event=None):

        # if the ListBox is not empty...
        if self.ListBox.GetCount() > 0:

            # Get the reference position
            index = int(self.ListBox.GetSelection())

            # Split the list into parts in front of and in back of the copy's 
            # insertion point.
            front = GLOBAL.Library.names[:index+1]
            back = GLOBAL.Library.names[index+1:]

            # Do the same for the list of community matrices in the library
            CMfront = GLOBAL.Library.CommunityMatrices[:index+1]
            CMback = GLOBAL.Library.CommunityMatrices[index+1:]
            
            # Produce the data clone
            COPY = deepcopy(GLOBAL.Library.CommunityMatrices[index])

            # Produce an appropriate and unique name
            Alternate = COPY.name
            for x in GLOBAL.Library.names:
                if Alternate == x:
                    while Alternate in GLOBAL.Library.names:
                        Alternate = Alternate+GLOBAL.language["dialog_DuplicateCM"][0]
            COPY.name = Alternate

            # Insert the entry into the list box, shift selection and update the display
            self.ListBox.Insert(COPY.name, index+1)
            for item in range(0,self.ListBox.GetCount()):
                self.ListBox.SetSelection(item, select = False)
            self.ListBox.SetSelection(index+1)

            # Insert the copied data into the Library
            GLOBAL.Library.CommunityMatrices = CMfront+[COPY]+CMback
            
            # Remake the Library names
            GLOBAL.Library.MakeNames()
            self.AddToHistory()
            self.UpdateDisplay()
            
    ##########
    # FUNCTION: EditCM
    def EditCM(self, Event=None):

        # if the ListBox is not empty...
        if int(self.ListBox.GetCount()) > 0:
            GLOBAL.Editindex = int(self.ListBox.GetSelection())

            # Copy the data of the currently selected CM 
            GLOBAL.EditA = GLOBAL.Library.CommunityMatrices[GLOBAL.Editindex].Data
            GLOBAL.EditName = deepcopy(GLOBAL.Library.CommunityMatrices[GLOBAL.Editindex].name)
            GLOBAL.EditNames = deepcopy(GLOBAL.Library.CommunityMatrices[GLOBAL.Editindex].names)
            
            # Invoke the Edit Community Matrix Dialog
            ECMdlg = NewCMDialog(self, -1, GLOBAL.language["dialog_EditCMDialog"][0], size=(350, 200),
                             style=wx.DEFAULT_DIALOG_STYLE
                             )
            ECMdlg.CenterOnScreen()
            ECMdlg.Bind(wx.EVT_CHAR_HOOK, None)
            # NCMdlg does not return until the dialog is closed.
            
            ##########
            # Handler for NCMdlg
            val = ECMdlg.ShowModal()

            if val == wx.ID_OK:

                # Show an alert if the DATA values are not present, and cancel the handler
                if ECMdlg.DATA.GetValue() == "":
                
                    alert = wx.MessageDialog( self, GLOBAL.language["dialog_EditCMDataAlert"][0][0],GLOBAL.language["dialog_EditCMDataAlert"][0][1], wx.OK)
                    alert.ShowModal() # Shows it
                    alert.Bind(wx.EVT_CHAR_HOOK, None)
                    ECMdlg.Destroy()
                    return

                ##########
                # Check upon presence of NAME and the duplicity of NAME in the library, 
                # modify as appropriate...
                
                # If NCMdlg.NAME.GetValue() is empty and unchanged replace it locally 
                # with "Matrix"...
                NAME = ECMdlg.NAME.GetValue()
                if NAME == "":
                    NAME = GLOBAL.language["dialog_EditCMName"][0]

                # If EMdlg.NAME.GetValue is not empty...
                # If there are ListBox elements and the ECMdlg.NAME.get() is not in 
                # GLOBAL.Library.names...
                if GLOBAL.Editindex != None:
                    if self.ListBox.GetCount() > 0 and NAME in GLOBAL.Library.names[:GLOBAL.Editindex]+GLOBAL.Library.names[GLOBAL.Editindex+1:]:
                        # ...and then appropriately increment the name "Matrix" if it is a 
                        # duplicate. 
                        Count = 2
                        for x in GLOBAL.Library.names:
                            if NAME == x:
                                while NAME+str(Count) in GLOBAL.Library.names:
                                    Count = Count + 1
                                NAME = NAME+" "+str(Count)
                    # Else if there are ListBox elements and the NCMdlg.NAME.get() _is_ in
                    # GLOBAL.Library.names, we just let the assignment of NAME to 
                    # ECMdlg.NAME.GetValue() stand.                

                ##########
                # Use the ECMdlg value to create a new communty matrix, and display it...

                # Instantiate a new CommunityMatrix with the provided values as 
                # appropriate for the presence or absence of names
                DATA = ECMdlg.DATA.GetValue()
# THIS CONDITIONAL SHOULD BE USED TO CHECK TO SEE WHETHER TO ACTUALLY RECALCULATE AFTER
# EDITING A COMMUNITY MATRIX (I.E. NO IF THE DATA ARE UNCHANGED)
#                if eval(DATA) == GLOBAL.Library.CommunityMatrices[GLOBAL.Editindex].Data:
                NAMES = ECMdlg.NAMES.GetValue()
                if NAMES == "":
                    CM = CommunityMatrix(eval(DATA),NAME)
                else:
                    CM = CommunityMatrix(eval(DATA),NAME,eval(NAMES))            
                
                if GLOBAL.Editindex == None:
                    self.AddNewCM(NAME)
                    GLOBAL.Library.AddCM(CM)
                else:
                    self.ListBox.Delete(GLOBAL.Editindex)
                    self.ListBox.Insert(NAME, GLOBAL.Editindex)
                    GLOBAL.Library.CommunityMatrices[GLOBAL.Editindex] = CM
                    GLOBAL.Library.names[GLOBAL.Editindex] = NAME
                    for item in range(0,self.ListBox.GetCount()):
                        self.ListBox.SetSelection(item, select = False)
                    self.ListBox.SetSelection(GLOBAL.Editindex, select = True)
### rewrite to make the below line happen only if the GetCount of the list 
### box is greater than the visible length of the listbox
#                    self.ListBox.SetFirstItem(GLOBAL.Editindex)
                    
                # Display the new CM
                self.UpdateDisplay()

            ECMdlg.Destroy()

            GLOBAL.Library.CommunityMatrices[GLOBAL.Editindex].Graph = []
            GLOBAL.Library.CommunityMatrices[GLOBAL.Editindex].GraphFlag = False
            if GLOBAL.Library.PrefsGraph == True:
                GLOBAL.Library.MakeGraph()
            self.AddToHistory()
            
            # Clean up
            GLOBAL.Editindex = None
            GLOBAL.EditA = ""
            GLOBAL.EditName = ""
            GLOBAL.EditNames = ""

    ##########
    # ClipCommunityMatrix
    def ClipCommunityMatrix(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipCM = str(GLOBAL.Library.CommunityMatrices[index].DisplayCM())
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipCM))
                wx.TheClipboard.Close()

    ##########
    # ClipGraph
    def ClipGraph(self, Event = None):
        if GLOBAL.Library.PrefsGraph == True and len(GLOBAL.Library.CommunityMatrices) > 0:
            index = self.ListBox.GetSelection()
            if len(GLOBAL.Library.CommunityMatrices) > 0:

                # Read the CM.Graphed png data into an StringIO, then read an image from 
                # that data stream.
                GraphImageStream = StringIO(GLOBAL.Library.CommunityMatrices[index].Graphed)
                GraphImage = wx.ImageFromStream(GraphImageStream, wx.BITMAP_TYPE_ANY)

                # Scale the graph.
                scale_factor = 1
                ClipWidth = 1024
                ClipHeight = float(GraphImage.GetHeight())*(ClipWidth/float(GraphImage.GetWidth()))
                GraphImage = GraphImage.Scale(ClipWidth,ClipHeight)

                # Write the image to the clipboard.
                if wx.TheClipboard.Open():
                    wx.TheClipboard.SetData(wx.BitmapDataObject(wx.BitmapFromImage(GraphImage,32)))
                    wx.TheClipboard.Close()

    ##########
    # ClipPredictions
    def ClipPredictions(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipPR = str(GLOBAL.Library.CommunityMatrices[index].DisplayCEM())
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipPR))
                wx.TheClipboard.Close()

    ##########
    # ClipAdjoint
    def ClipAdjoint(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipAdjoint = GLOBAL.Library.CommunityMatrices[index].DisplayAdjoint()+"\n"+GLOBAL.Library.CommunityMatrices[index].DisplayT()
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipAdjoint))
                wx.TheClipboard.Close()

    ##########
    # ClipWFM
    def ClipWFM(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipWFM = GLOBAL.Library.CommunityMatrices[index].DisplayWFM()
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipWFM))
                wx.TheClipboard.Close()

    ##########
    # ClipWPM
    def ClipWPM(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipWPM = GLOBAL.Library.CommunityMatrices[index].DisplayWPM()
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipWPM))
                wx.TheClipboard.Close()

    ##########
    # ClipCLEM
    def ClipCLEM(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipCLEM = GLOBAL.Library.CommunityMatrices[index].DisplayCLEM()
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipCLEM))
                wx.TheClipboard.Close()
            
    ##########
    # ClipAll
    def ClipAll(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipCM = str(GLOBAL.Library.CommunityMatrices[index].DisplayCM())
            ClipPR = str(GLOBAL.Library.CommunityMatrices[index].DisplayCEM())
            ClipAdjoint = GLOBAL.Library.CommunityMatrices[index].DisplayAdjoint()+"\n"+GLOBAL.Library.CommunityMatrices[index].DisplayT()
            ClipWFM = GLOBAL.Library.CommunityMatrices[index].DisplayWFM()
            ClipWPM = GLOBAL.Library.CommunityMatrices[index].DisplayWPM()
            ClipCLEM = GLOBAL.Library.CommunityMatrices[index].DisplayCLEM()
            ClipCO = GLOBAL.Library.CommunityMatrices[index].DisplayCorrelations()
            ClipPaths = GLOBAL.Library.CommunityMatrices[index].DisplayPaths()
            ClipLoops = GLOBAL.Library.CommunityMatrices[index].DisplayLoops()
            ClipAll = ClipCM+"\n"+ClipPR+"\n"+ClipAdjoint+"\n"+ClipWFM+"\n"+ClipWPM+"\n"+ClipCLEM+"\n"+ClipCO+"\n"+ClipPaths+"\n"+ClipLoops
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipAll))
                wx.TheClipboard.Close()
        
    ##########
    # ClipCorrelations
    def ClipCorrelations(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipCorrelations = str(GLOBAL.Library.CommunityMatrices[index].DisplayCorrelations())
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipCorrelations))
                wx.TheClipboard.Close()

    ##########
    # ClipPaths
    def ClipPaths(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipPaths = str(GLOBAL.Library.CommunityMatrices[index].DisplayPaths())
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipPaths))
                wx.TheClipboard.Close()

    ##########
    # ClipLoops
    def ClipLoops(self, Event = None):
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            ClipLoops = str(GLOBAL.Library.CommunityMatrices[index].DisplayLoops())
            if wx.TheClipboard.Open():
                wx.TheClipboard.SetData(wx.TextDataObject(ClipLoops))
                wx.TheClipboard.Close()

    ##########
    # FUNCTION: About
    def About(self, Event = None):
        About = AboutDialog(self, -1, "", style=wx.DEFAULT_DIALOG_STYLE | wx.STAY_ON_TOP)
        About.CenterOnScreen()
        About.Bind(wx.EVT_CHAR_HOOK, None)
        
        # About does not return until the dialog is closed.
        About.ShowModal()

        About.Destroy()

    ##########
    # FUNCTION: Help
    def Help(self, Event = None):
        Help = HelpDialog(self, -1, "", style=wx.DEFAULT_DIALOG_STYLE)
        Help.CenterOnScreen()
        Help.Bind(wx.EVT_CHAR_HOOK, None)
        
        # Help does not return until the dialog is closed.
        Value = Help.ShowModal()

        Help.Destroy()
        

    ############################################################################
    ### AppUI MISCELLANEOUS FUNCTIONS                                        ###
    ############################################################################


    ##########
    # FUNCTION: ParseLA1
    def ParseLA1(self, line):
        # Strip some spaces
        line = line.replace(" [","[")
        line = line.replace(" ]","]")
        line = line.replace("[ ","[")
        line = line.replace("] ","]")
        # Replace single quotes with double quotes
        line = line.replace("\'","\"")
        # Guess at the validity of the line based on start and end characters
        if (line.startswith("[[[") == False):
            return False
        if (line.endswith("]]") == False):
            return False
        # Separate the Data, Names, and N sections into separate variables
        Data = line[1:line.find("]]")+2]
        Names = line[line.find("]],")+4:line.rfind("],[",0,line.rfind("],["))]
        N = int(line[line.rfind("],[",0,line.rfind("],["))+3:line.rfind("],[")])
        Name = line[line.rfind("],[")+4:-3]
        # Strip whitespaces, and recode
        Data = Data.replace(" ","").replace(",+,",",1,").replace("[+,","[1,").replace("+]","1]").replace(",-,",",-1,").replace("[-,","[-1,").replace("-]","-1]").replace("+1","1")
        # Validate Data
        if (Data.startswith("[[") == False):
            return False
        if (Data.endswith("]]") == False):
            return False
        if (Data.count("],[") != N-1):
            return False
        if (Data.count(",") != (N*N - 1)):
            return False
        test = Data.replace("[","").replace("1","").replace("+","").replace("0","").replace(" ","").replace("-","").replace(",","").replace("]","")
        if (test != ""):
            return False
        # Bye!
        return [Data[1:-1],Names,Name]

    ##########
    # FUNCTION: findn
    # findn() returns the index of the nth occurence of sub in string
    def findn(string, sub, n):
        index = 0
        cumindex = -1
        while index < n:
            cumindex = string.find(sub, cumindex+1)
            if cumindex == -1: 
                return -1
            index = index+1
        return cumindex

    ##########
    # FUNCTION: bracketize
    # bracketize takes a vector of values comprising a comunity matrix
    # and returns them in a pythonic array form
    def bracketize(self, string, n):
        for i in range(0,n-1):
            string = string.replace(",","],[",n*(n-(i+1))).replace("],[",",",n*(n-(i+1))-1)
        return "[["+string+"]]"

    ##########
    # FUNCTION: ParseMaple
    def ParseMaple(self, line):
        # Strip spaces
        line = line.replace(" ","")
        # Guess at the validity of the line based on start and end characters
        if (line.find(":=array(") == -1):
            return False
        if (line.endswith("));") == False):
            return False
        # Separate the Data, Names, and N sections into separate variables
        Names = ""
        N = line[line.find("..")+2:line.find(",1..")]
        if (N.isdigit()):
            N = int(N)
        else:
            N = int(line[line.find(N+":=")+len(N)+2:line.find(":",line.find(N+":=")+len(N)+2)])
        Data = self.bracketize(line[line.find("c(")+2:-3],N)
        Name = line[:line.find(":=array")][line[:line.find(":=array")].rfind(":")+1:]
        # Strip whitespaces, and recode
        Data = Data.replace("+1","1")
        # Validate Data
        if (Data.startswith("[[") == False):
            return False
        if (Data.endswith("]]") == False):
            return False
        if (Data.count("],[") != N-1):
            return False
        if (Data.count(",") != (N*N - 1)):
            return False
        test = Data.replace("[","").replace("1","").replace("+","").replace("0","").replace(" ","").replace("-","").replace(",","").replace("]","")
        if (test != ""):
            return False
        # Bye!
        return [Data[1:-1],Names,Name]

    ##########
    # FUNCTION: ParseR
    def ParseR(self, line):
        # Strip spaces
        line = line.replace(" ","").replace("<-","=")
        # Guess at the validity of the line based on start and end characters
        if (line.find("matrix(c(") == -1):
            return False
        if (line.endswith(")") == False):
            return False
        # Separate the Data, Names, and N sections into separate variables
        Names = line[line.find("dimnames")+16:line.rfind("),c(")]
        N = int(line[line.find("nrow=")+5:line.find(",",line.find("nrow=")+5)])
        Data = self.bracketize(line[line.find("(c(")+3:line.find("),")],N)
        Name = line[:line.find("=matrix")]
        # Strip whitespaces, and recode
        Data = Data.replace("+1","1")
        # Validate Data
        if (line.find("byrow=TRUE") == -1):
            return -1
        if (Data.startswith("[[") == False):
            return False
        if (Data.endswith("]]") == False):
            return False
        if (Data.count("],[") != N-1):
            return False
        if (Data.count(",") != (N*N - 1)):
            return False
        test = Data.replace("[","").replace("1","").replace("+","").replace("0","").replace(" ","").replace("-","").replace(",","").replace("]","")
        if (test != ""):
            return False
        # Bye!
        return [Data[1:-1],Names,Name]

    ##########
    # FUNCTION: ResetHistory
    # ResetHistory sets the HistoryIndex to 0 and initializes the History
    # with the value of the current Library
    def ResetHistory(self):
        GLOBAL.HistoryIndex = 0
        GLOBAL.Library.Name = GLOBAL.LibraryName
        GLOBAL.History = [deepcopy(GLOBAL.Library)]

    ##########
    # FUNCTION: CropFuture
    # CropFuture erases all Libraries in History with numbers greater than the
    # current index.
    def CropFuture(self):
        GLOBAL.History = GLOBAL.History[:GLOBAL.HistoryIndex+1]

    ##########
    # FUNCTION: AddToHistory
    # AddToHistory appends the current Library to the history at the curent index.
    # It checks first to see if the future should be cropped
    def AddToHistory(self):
        if GLOBAL.HistoryIndex < len(GLOBAL.History) - 1:
            self.CropFuture()
        GLOBAL.Library.Name = GLOBAL.LibraryName
        GLOBAL.History = GLOBAL.History + [deepcopy(GLOBAL.Library)]
        GLOBAL.HistoryIndex = len(GLOBAL.History) - 1

    ##########
    # FUNCTION: ReturnFile
    # Takes a string representing a /path/to/a/file and returns just the "file" 
    # portion
    def ReturnFile(self, path):
        reversed = list(path)
        reversed.reverse()
        reversed = ''.join(reversed)
        file = ""
        for char in reversed:
            if char != "/":
                file = char+file
            if char == "/":
                return(file)
                
    ##########
    # FUNCTION: AddRecentLibrary
    # Takes a string representing a /path/to/a/file, checks if it is in
    # GLOBAL.RecentLibraries, removes it from the history if it is present 
    # already, and adds it to the front whether it is present already or not.
    # Finally, GLOBAL.RecentLibraries is pared down to be no greater than the 
    # length of GLOBAL.RecentLibrariesListLength
    def AddRecentLibrary(self, path):
        # remove the path if it is already in GLOBAL.RecentLibraries
        if path in GLOBAL.RecentLibraries:
            if len(GLOBAL.RecentLibraries) == 1:
                GLOBAL.RecentLibraries = GLOBAL.RecentLibraries
            else:
                Temp = deepcopy(GLOBAL.RecentLibraries)
                Temp.reverse()
                for x in range(0,len(GLOBAL.RecentLibraries)):
                    if Temp[x] == path:
                        del GLOBAL.RecentLibraries[len(Temp)-x-1]

                # Prepend path to GLOBAL.RecentLibraries
                GLOBAL.RecentLibraries = [path]+GLOBAL.RecentLibraries
        else:
            if len(GLOBAL.RecentLibraries) == 0:
                GLOBAL.RecentLibraries = [path]
            else:
                GLOBAL.RecentLibraries = [path]+GLOBAL.RecentLibraries
        
        # Truncate GLOBAL.RecentLibraries to the appropriate size if need be
        if len(GLOBAL.RecentLibraries) > GLOBAL.RecentLibrariesListLength:
            del GLOBAL.RecentLibraries[GLOBAL.RecentLibrariesListLength:len(GLOBAL.RecentLibraries)]
        
        # Remove previous recent menu entries
        #for x in range(22,self.MenuBar.GetMenu(0).GetMenuItemCount()+1):
            #self.MenuBar.GetMenu(0).DestroyItem(self.MenuBar.GetMenu(0).FindItemByPosition(21))
        # Display the new menu items
#        self.AppendRecentLibraries()
        
        # Update the preferences
        self.UpdatePreferences()
        self.Menubar()

    ##########
    # AppendRecentLibraries
    def AppendRecentLibraries(self):
        for path in GLOBAL.RecentLibraries:
            self.MenuBar.GetMenu(0).Append(wx.NewId(), self.ReturnFile(path))
        for item in range(0,len(GLOBAL.RecentLibraries)):
            ItemId = self.MenuBar.GetMenu(0).FindItem(self.ReturnFile(GLOBAL.RecentLibraries[item]))


    ##########
    # OpenRecent
    def OpenRecent(self, index, Event = None):
        # Add the path to the GLOBAL.RecentLibraries (this updates preferences)
        # Clear listbox
        self.ListBox.Clear()

        # Import Library
        FILE = file(GLOBAL.RecentLibraries[index],'r')
        GLOBAL.Library = load(FILE)
        FILE.close()
        GLOBAL.LibraryLastSaved = deepcopy(GLOBAL.Library)
        GLOBAL.Library.names = []
        for x in GLOBAL.Library.CommunityMatrices:
            # Add the name to the listbox
            self.AddNewCM(x.name)
            # Reconstruct the Library.names
            GLOBAL.Library.names = GLOBAL.Library.names+[x.name]
        self.ListBox.SetSelection(self.ListBox.GetCount(), select = True)

        # Display the new CM
        self.SetTitle("Loop Analyst: "+GLOBAL.LibraryName)
        if not Launch:
            self.UpdateDisplay()

    ##########
    # FUNCTION: ReviseCMText
    # Returns
    def ReviseCMText(self):
        if len(GLOBAL.Library.CommunityMatrices) == 0:
            return ""
        if len(GLOBAL.Library.CommunityMatrices) > 0:
            index = int(self.ListBox.GetSelection())
            return GLOBAL.Library.CommunityMatrices[index].DisplayCM()

    ##########
    # FUNCTION: ReviseCEMText
    # Returns
    def ReviseCEMText(self):
        if len(GLOBAL.Library.CommunityMatrices) == 0:
            return ""
        index = int(self.ListBox.GetSelection())
        if len(GLOBAL.Library.CommunityMatrices) > 0 and GLOBAL.Library.CommunityMatrices[index].CEMFlag == True:
            return GLOBAL.Library.CommunityMatrices[index].DisplayCEM()

    ##########
    # FUNCTION: ReviseAdjointText
    # Returns
    def ReviseAdjointText(self):
        if len(GLOBAL.Library.CommunityMatrices) == 0:
            return ""
        index = int(self.ListBox.GetSelection())
        if len(GLOBAL.Library.CommunityMatrices) > 0 and GLOBAL.Library.PrefsAdjoint == True:
            return str(GLOBAL.Library.CommunityMatrices[index].DisplayAdjoint())+"\n"+str(GLOBAL.Library.CommunityMatrices[index].DisplayT())

    ##########
    # FUNCTION: ReviseWFMText
    # Returns
    def ReviseWFMText(self):
        if len(GLOBAL.Library.CommunityMatrices) == 0:
            return ""
        index = int(self.ListBox.GetSelection())
        if len(GLOBAL.Library.CommunityMatrices) > 0 and GLOBAL.Library.PrefsWFM == True:
            return str(GLOBAL.Library.CommunityMatrices[index].DisplayWFM())

    ##########
    # FUNCTION: ReviseWPMText
    # Returns
    def ReviseWPMText(self):
        if len(GLOBAL.Library.CommunityMatrices) == 0:
            return ""
        index = int(self.ListBox.GetSelection())
        if len(GLOBAL.Library.CommunityMatrices) > 0 and GLOBAL.Library.CommunityMatrices[index].WPMFlag == True:
            return GLOBAL.Library.CommunityMatrices[index].DisplayWPM()

    ##########
    # FUNCTION: ReviseCLEMText
    # Returns
    def ReviseCLEMText(self):
        if len(GLOBAL.Library.CommunityMatrices) == 0:
            return ""
        index = int(self.ListBox.GetSelection())
        if len(GLOBAL.Library.CommunityMatrices) > 0 and GLOBAL.Library.CommunityMatrices[index].CLEMFlag == True:
            return GLOBAL.Library.CommunityMatrices[index].DisplayCLEM()

    ##########
    # FUNCTION: UpdatePreferences
    def UpdatePreferences(self):
        # Update preference values
        PERSISTENT.Persistence[0] = deepcopy(GLOBAL.RecentDirectory)
        PERSISTENT.Persistence[1] = deepcopy(GLOBAL.RecentLibraries)
        PERSISTENT.Persistence[2] = deepcopy(GLOBAL.RecentLibrariesListLength)
        if len(PERSISTENT.Persistence) > 3:
            PERSISTENT.Persistence[3] = deepcopy(GLOBAL.GraphColoring)
        else:
            PERSISTENT.Persistence = PERSISTENT.Persistence+[deepcopy(GLOBAL.GraphColoring)]
        if len(PERSISTENT.Persistence) > 5:
            PERSISTENT.Persistence[4] = deepcopy(GLOBAL.DisplayFontSize)
            PERSISTENT.Persistence[5] = deepcopy(GLOBAL.WeightedPredictionThreshold)
            PERSISTENT.Persistence[6] = deepcopy(GLOBAL.ThresholdCriterion)
        else:
            PERSISTENT.Persistence = PERSISTENT.Persistence+[deepcopy(GLOBAL.DisplayFontSize),deepcopy(GLOBAL.WeightedPredictionThreshold),deepcopy(GLOBAL.ThresholdCriterion)]
        if len(PERSISTENT.Persistence) > 8:
            PERSISTENT.Persistence[7] = self.GetPosition()
            PERSISTENT.Persistence[8] = self.GetSize()
        else:
            PERSISTENT.Persistence = PERSISTENT.Persistence+[deepcopy(GLOBAL.Position),deepcopy(GLOBAL.Size)]
        if len(PERSISTENT.Persistence) > 9:
            PERSISTENT.Persistence[9] = deepcopy(GLOBAL.WeightedFeedbackPrecision)
        else:
            PERSISTENT.Persistence = PERSISTENT.Persistence+[deepcopy(GLOBAL.WeightedFeedbackPrecision)]
        if len(PERSISTENT.Persistence) > 10:
            PERSISTENT.Persistence[10] = deepcopy(GLOBAL.dotLocation)
        else:
            PERSISTENT.Persistence = PERSISTENT.Persistence+[deepcopy(GLOBAL.dotLocation)]
        if len(PERSISTENT.Persistence) > 11:
            PERSISTENT.Persistence[11] = deepcopy(GLOBAL.Language)
        else:
            PERSISTENT.Persistence = PERSISTENT.Persistence+[deepcopy(GLOBAL.Language)]

        # Save the updated values
        self.Preferences = str(wx.StandardPaths.Get().GetUserConfigDir())+"/Loop Analyst.prefs"
        Prefs = file(self.Preferences,'w')
        dump(PERSISTENT.Persistence, Prefs, 1)
        Prefs.close()

    def getData(self):
        return b64decode(GLOBAL.SplashData)

    def getBitmap(self):
        return BitmapFromImage(self.getImage())

    def getImage(self):
        stream = StringIO(self.getData())
        return ImageFromStream(stream)

########################################
# Preferences Dialog
class PreferencesDialog(wx.Dialog):
    def __init__(self, parent, ID, title, size=wx.DefaultSize, pos=wx.DefaultPosition, style=wx.DEFAULT_DIALOG_STYLE):
    
        pre = wx.PreDialog()
        pre.SetExtraStyle(wx.DIALOG_EX_CONTEXTHELP)
        pre.Create(parent, ID, title, pos, size, style)
        
        self.PostCreate(pre)
        
        # initialize the geometry
        sizer = wx.BoxSizer(wx.VERTICAL)

        # Font used for headers in the preferences dialog
        PreferencesDisplayFont = wx.Font(12, wx.MODERN, wx.NORMAL, wx.BOLD)

        # Add radio box for graph colors
        GraphColorRadioboxLabel = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_PreferencesGraphColor"][0])
        label.SetFont(PreferencesDisplayFont)
        GraphColorRadioboxLabel.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(GraphColorRadioboxLabel, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        self.ColorChoices = GLOBAL.language["dialog_PreferencesGraphColorChoices"][0]
        self.ColorSchemeRadiobox = wx.RadioBox(self, id=-1, size = wx.DefaultSize, pos= wx.DefaultPosition, choices=self.ColorChoices, style=wx.VERTICAL)
        self.ColorSchemeRadiobox.SetSelection(GLOBAL.GraphColoring)
        self.ColorSchemeRadiobox.SetFont(PreferencesDisplayFont)
        sizer.Add(self.ColorSchemeRadiobox, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.RIGHT|wx.LEFT|wx.TOP, 1)

        sizer.Add(wx.StaticLine(self, -1), 0, wx.EXPAND)
        
        # Add the text control for the path to graphviz's dot command
        GraphvizBoxLabel = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_PreferencesGraphvizPath"][0])
        label.SetHelpText(GLOBAL.language["dialog_PreferencesGraphvizPathHelp"][0])
        label.SetFont(PreferencesDisplayFont)
        GraphvizBoxLabel.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(GraphvizBoxLabel, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        GraphvizBox = wx.BoxSizer(wx.HORIZONTAL)
        self.dotpath = wx.TextCtrl(self, -1, GLOBAL.dotLocation, size=(80,-1))
        self.dotpath.SetHelpText(GLOBAL.language["dialog_PreferencesGraphvizPathHelp"][0])
        GraphvizBox.Add(self.dotpath, 1, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(GraphvizBox, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        sizer.Add(wx.StaticLine(self, -1), 0, wx.EXPAND)

        # Add the text control for the display font size
        FontSizeBoxLabel = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_PreferencesFontSize"][0])
        label.SetFont(PreferencesDisplayFont)
        FontSizeBoxLabel.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(FontSizeBoxLabel, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        FontSizeBox = wx.BoxSizer(wx.HORIZONTAL)
        self.displayfontsize = wx.TextCtrl(self, -1, str(GLOBAL.DisplayFontSize), size=(80,-1))
        FontSizeBox.Add(self.displayfontsize, 1, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(FontSizeBox, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        sizer.Add(wx.StaticLine(self, -1), 0, wx.EXPAND)

        # Add the text control for the display precision of weighted feedback
        WeightedFeedbackPrecisionBoxLabel = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_PreferencesWFPrecision"][0])
        label.SetFont(PreferencesDisplayFont)
        WeightedFeedbackPrecisionBoxLabel.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(WeightedFeedbackPrecisionBoxLabel, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        WeightedFeedbackPrecisionBox = wx.BoxSizer(wx.HORIZONTAL)
        self.weightedfeedbackprecision = wx.TextCtrl(self, -1, str(GLOBAL.WeightedFeedbackPrecision), size=(80,-1))
        WeightedFeedbackPrecisionBox.Add(self.weightedfeedbackprecision, 1, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(WeightedFeedbackPrecisionBox, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        sizer.Add(wx.StaticLine(self, -1), 0, wx.EXPAND)

        # Add radio box and value field for weighted predictions threshold
        ThresholdRadioboxLabel = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_PreferencesWFCriterion"][0])
        label.SetFont(PreferencesDisplayFont)
        ThresholdRadioboxLabel.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(ThresholdRadioboxLabel, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)
        
        self.ThresholdChoices = [GLOBAL.language["dialog_PreferencesWFPrecisionChoices"][0][0],GLOBAL.language["dialog_PreferencesWFPrecisionChoices"][0][1]]
        self.ThresholdRadiobox = wx.RadioBox(self, id=-1, size = wx.DefaultSize, pos= wx.DefaultPosition, choices=self.ThresholdChoices, style=wx.VERTICAL)
        self.ThresholdRadiobox.SetSelection(GLOBAL.ThresholdCriterion)
        self.ThresholdRadiobox.SetFont(PreferencesDisplayFont)
        sizer.Add(self.ThresholdRadiobox, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.RIGHT|wx.LEFT|wx.TOP, 1)
        
        WeightedPredictionsThresholdBoxLabel = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_PreferencesWFThreshold"][0])
        label.SetFont(PreferencesDisplayFont)
        WeightedPredictionsThresholdBoxLabel.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(WeightedPredictionsThresholdBoxLabel, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        WeightedPredictionsThresholdBox = wx.BoxSizer(wx.HORIZONTAL)
        self.weightedpredictionthreshold = wx.TextCtrl(self, -1, str(GLOBAL.WeightedPredictionThreshold), size=(80,-1))
        WeightedPredictionsThresholdBox.Add(self.weightedpredictionthreshold, 1, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(WeightedPredictionsThresholdBox, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        sizer.Add(wx.StaticLine(self, -1), 0, wx.EXPAND)

        # Add radio box for internationalization
        LanguageRadioboxLabel = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_PreferencesLanguage"][0])
        label.SetFont(PreferencesDisplayFont)
        LanguageRadioboxLabel.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 1)
        sizer.Add(LanguageRadioboxLabel, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 1)

        self.LanguageChoices = GLOBAL.language["dialog_PreferencesLanguageChoices"][0]
        self.LanguageRadiobox = wx.RadioBox(self, id=-1, size = wx.DefaultSize, pos= wx.DefaultPosition, choices=self.LanguageChoices, style=wx.VERTICAL)
        self.LanguageRadiobox.SetSelection(GLOBAL.Language)
        self.LanguageRadiobox.SetFont(PreferencesDisplayFont)
        sizer.Add(self.LanguageRadiobox, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.RIGHT|wx.LEFT|wx.TOP, 1)

        # Create Help, Cancel and OK buttons
        ButtonSizer = wx.StdDialogButtonSizer()

        if wx.Platform != "__WXMSW__":
            Helpbtn = wx.ContextHelpButton(self)
            ButtonSizer.AddButton(Helpbtn)

        OKbtn = wx.Button(self, wx.ID_OK)
        OKbtn.SetDefault()
        ButtonSizer.AddButton(OKbtn)

        Cancelbtn = wx.Button(self, wx.ID_CANCEL)
        ButtonSizer.AddButton(Cancelbtn)
        ButtonSizer.Realize()

        sizer.Add(ButtonSizer, 4, wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)

        self.SetSizer(sizer)
        sizer.Fit(self)
        self.Raise()


########################################
# About Dialog
class AboutDialog(wx.Dialog):
    def __init__(self, parent, ID, title, size=wx.DefaultSize, pos=wx.DefaultPosition, style=wx.DEFAULT_DIALOG_STYLE):
        pre = wx.PreDialog()
        pre.SetExtraStyle(wx.DIALOG_EX_CONTEXTHELP)
        pre.Create(parent, ID, title, pos, size, style)
        
        self.PostCreate(pre)
        
        # initialize the geometry
        sizer = wx.BoxSizer(wx.VERTICAL)

        AboutSizer = wx.BoxSizer(wx.VERTICAL)

        icon = wx.StaticBitmap(self, -1, self.getIconBitmap())
        AboutSizer.Add(icon, 0, wx.ALIGN_CENTER)

        title = wx.StaticText(self, -1, "Loop Analyst")
        title.SetFont(wx.Font(15, wx.SWISS, wx.NORMAL, wx.BOLD))
        AboutSizer.Add(title, 0, wx.ALIGN_CENTER|wx.ALL, 10)

        version = wx.StaticText(self, -1, GLOBAL.language["dialog_AboutVersion"][0]+str(Version)+"\n\n" +GLOBAL.language["dialog_AboutAuthor"][0]+"\n")
        version.SetFont(wx.Font(12, wx.SWISS, wx.NORMAL, wx.NORMAL))
        AboutSizer.Add(version, 0, wx.ALIGN_CENTER|wx.ALL)

        mail = wx.HyperlinkCtrl(self, -1, label = "alexis.dinno@pdx.edu", url = "mailto:alexis.dinno@pdx.edu")
        mail.SetFont(wx.Font(12, wx.SWISS, wx.NORMAL, wx.NORMAL, underline=True))
        mail.SetNormalColour(wx.Colour(0, 0, 255, 255))
        mail.SetVisitedColour(wx.Colour(0, 0, 255, 255))
        mail.SetHoverColour(wx.Colour(0, 0, 255, 255))
        AboutSizer.Add(mail, 0, wx.ALIGN_CENTRE|wx.ALL)

        body = wx.StaticText(self, -1, GLOBAL.language["dialog_AboutBody"][0])
        body.Wrap(420)
        body.SetFont(wx.Font(12, wx.SWISS, wx.NORMAL, wx.NORMAL))
        AboutSizer.Add(body, 0, wx.ALIGN_LEFT|wx.ALL)

        link = wx.HyperlinkCtrl(self, -1, label = "http://www.alexisdinno.com/LoopAnalyst", url = "http://www.alexisdinno.com/LoopAnalyst")
        link.SetFont(wx.Font(12, wx.SWISS, wx.NORMAL, wx.NORMAL, underline=True))
        link.SetNormalColour(wx.Colour(0, 0, 255, 255))
        link.SetVisitedColour(wx.Colour(0, 0, 255, 255))
        link.SetHoverColour(wx.Colour(0, 0, 255, 255))
        AboutSizer.Add(link, 0, wx.ALIGN_CENTRE|wx.ALL)
        sizer.Add(AboutSizer, 0, wx.ALIGN_CENTER_VERTICAL|wx.ALL, 10)

        # Create OK button
        ButtonSizer = wx.StdDialogButtonSizer()
        OKButton = wx.Button(self, wx.ID_OK)
        OKButton.SetDefault()
        ButtonSizer.AddButton(OKButton)
        ButtonSizer.Realize()
        sizer.Add(ButtonSizer, 4, wx.ALIGN_CENTER|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)

        self.SetSizer(sizer)
        sizer.Fit(self)
        self.Raise()

    def getIconData(self):
        return b64decode(GLOBAL.IconData)

    def getIconBitmap(self):
        return BitmapFromImage(self.getIconImage())

    def getIconImage(self):
        stream = StringIO(self.getIconData())
        return ImageFromStream(stream)




########################################
# New Community Matrix Dialog

class NewCMDialog(wx.Dialog):
    def __init__(self, parent, ID, title, size=wx.DefaultSize, pos=wx.DefaultPosition, style=wx.DEFAULT_DIALOG_STYLE):

        pre = wx.PreDialog()
        pre.SetExtraStyle(wx.DIALOG_EX_CONTEXTHELP)
        pre.Create(parent, ID, title, pos, size, style)

        self.PostCreate(pre)

        # initialize the geometry
        sizer = wx.BoxSizer(wx.VERTICAL)

        # Name
        # Get edit name. . . 
        EditNAME = ""
        if GLOBAL.EditName != "":
            EditNAME = str(GLOBAL.EditName)

        box = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_NewCMDialogName"][0])
        label    .SetHelpText(GLOBAL.language["dialog_NewCMDialogNameMessage"][0])
        box.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 5)
        sizer.Add(box, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)

        box = wx.BoxSizer(wx.HORIZONTAL)
        self.NAME = wx.TextCtrl(self, -1, EditNAME, size=(80,-1))
        self.NAME.SetHelpText(GLOBAL.language["dialog_NewCMDialogNameMessage"][0])
        box.Add(self.NAME, 1, wx.ALIGN_CENTRE|wx.ALL, 5)
        sizer.Add(box, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)

        # Data
        # Get edit data. . .
        EditA = ""
        GLOBAL.EditA = str(GLOBAL.EditA)[1:][:-1].replace(" ","")        
        if GLOBAL.EditA != "":
            EditA = "["+str(GLOBAL.EditA)+"]"

        box = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_NewCMDialogData"][0])
        label.SetHelpText(GLOBAL.language["dialog_NewCMDialogDataMessage"][0])
        box.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 5)
        sizer.Add(box, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)
        
        box = wx.BoxSizer(wx.HORIZONTAL)
        self.DATA = wx.TextCtrl(self, -1, EditA, size=(80,-1))
        self.DATA.SetHelpText(GLOBAL.language["dialog_NewCMDialogDataMessage"][0])
        box.Add(self.DATA, 1, wx.ALIGN_CENTRE|wx.ALL, 5)
        sizer.Add(box, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)

        # Variable names
        EditNAMES = ""
        if GLOBAL.EditNames != "":
            EditNAMES = str(GLOBAL.EditNames)

        box = wx.BoxSizer(wx.HORIZONTAL)
        label = wx.StaticText(self, -1, GLOBAL.language["dialog_NewCMDialogVarNames"][0])
        label.SetHelpText(GLOBAL.language["dialog_NewCMDialogVarNamesMessage"][0])
        box.Add(label, 0, wx.ALIGN_CENTRE|wx.ALL, 5)
        sizer.Add(box, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)
        
        box = wx.BoxSizer(wx.HORIZONTAL)
        self.NAMES = wx.TextCtrl(self, -1, EditNAMES, size=(80,-1))
        self.NAMES.SetHelpText(GLOBAL.language["dialog_NewCMDialogVarNamesMessage"][0])
        box.Add(self.NAMES, 1, wx.ALIGN_CENTRE|wx.ALL, 5)
        sizer.Add(box, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)

        line = wx.StaticLine(self, -1, size=(20,-1), style=wx.LI_HORIZONTAL)
        sizer.Add(line, 0, wx.GROW|wx.ALIGN_CENTER_VERTICAL|wx.RIGHT|wx.TOP, 5)

        ButtonSizer = wx.StdDialogButtonSizer()

        if wx.Platform != "__WXMSW__":
            Helpbtn = wx.ContextHelpButton(self)
            ButtonSizer.AddButton(Helpbtn)

        OKbtn = wx.Button(self, wx.ID_OK)
        OKbtn.SetDefault()
        ButtonSizer.AddButton(OKbtn)

        Cancelbtn = wx.Button(self, wx.ID_CANCEL)
        ButtonSizer.AddButton(Cancelbtn)
        ButtonSizer.Realize()

        sizer.Add(ButtonSizer, 0, wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)

        self.SetSizer(sizer)
        sizer.Fit(self)
        self.Raise()


########################################
# Help Dialog
class HelpDialog(wx.Dialog):
    def __init__(self, parent, ID, title, size=wx.DefaultSize, pos=wx.DefaultPosition, style=wx.DEFAULT_DIALOG_STYLE):
    
        pre = wx.PreDialog()
        pre.Create(parent, ID, title, pos, size, style)
        
        self.PostCreate(pre)
        
        # initialize the geometry
        sizer = wx.BoxSizer(wx.VERTICAL)

        HelpSizer = wx.BoxSizer(wx.VERTICAL)

        title = wx.StaticText(self, -1, GLOBAL.language["dialog_HelpTitle"][0])
        title.SetFont(wx.Font(15, wx.SWISS, wx.NORMAL, wx.BOLD))
        HelpSizer.Add(title, 0, wx.ALIGN_CENTER|wx.ALL, 10)

        body = wx.StaticText(self, -1, GLOBAL.language["dialog_HelpBody"][0])
        body.SetFont(wx.Font(12, wx.SWISS, wx.NORMAL, wx.NORMAL))
        HelpSizer.Add(body, 0, wx.ALIGN_LEFT|wx.ALL)

        link = wx.HyperlinkCtrl(self, -1, label = "http://www.alexisdinno.com/LoopAnalyst/help.shtml", url = "http://www.alexisdinno.com/LoopAnalyst/help.shtml")
        link.SetNormalColour(wx.Colour(0, 0, 255, 255))
        link.SetVisitedColour(wx.Colour(0, 0, 255, 255))
        link.SetHoverColour(wx.Colour(0, 0, 255, 255))
        link.SetFont(wx.Font(12, wx.SWISS, wx.NORMAL, wx.NORMAL))
        HelpSizer.Add(link, 0, wx.ALIGN_CENTRE|wx.ALL)
        sizer.Add(HelpSizer, 0, wx.ALIGN_CENTER_VERTICAL|wx.ALL, 10)

        # Create OK button
        ButtonSizer = wx.StdDialogButtonSizer()
        OKButton = wx.Button(self, wx.ID_OK)
        OKButton.SetDefault()
        ButtonSizer.AddButton(OKButton)
        ButtonSizer.Realize()
        sizer.Add(ButtonSizer, 4, wx.ALIGN_CENTER|wx.ALIGN_CENTER_VERTICAL|wx.ALL, 5)

        self.SetSizer(sizer)
        sizer.Fit(self)
        self.Raise()

########################################
# Falsy Dialog
class FalsyDialog(wx.Dialog):
    def __init__(self):
        wx.Dialog.__init__(self, None, title=" ")
        
        timer = wx.Timer(self)
        self.Bind(wx.EVT_TIMER, self.OnTimer, timer)
        timer.Start(1)
        self.Show()

    def OnTimer(self, event):
        self.Destroy()

########################################
# Confirm Dialog
class ConfirmDialog(wx.Dialog):
    def __init__(self, parent, ID, title, message, save=False, size=wx.DefaultSize, pos=wx.DefaultPosition, style=wx.DEFAULT_DIALOG_STYLE):
    
        pre = wx.PreDialog()
        pre.Create(parent, ID, title, pos, size, style)
        
        self.PostCreate(pre)
        
        # initialize the geometry
        sizer = wx.BoxSizer(wx.VERTICAL)

        ConfirmSizer = wx.BoxSizer(wx.VERTICAL)

        title = wx.StaticText(self, -1, message)
        title.SetFont(wx.Font(15, wx.SWISS, wx.NORMAL, wx.NORMAL))
        ConfirmSizer.Add(title, 0, wx.ALIGN_CENTER|wx.ALL)
        sizer.Add(ConfirmSizer, 0, wx.ALIGN_CENTER_VERTICAL|wx.ALL, 10)        


        # Set up the buttons!
        ButtonSizer = wx.BoxSizer(wx.HORIZONTAL)

        ButtonSizer.Add((50,0),0)

        # Create Cancel button
        CancelButton = wx.Button(self, wx.ID_CANCEL)
        ButtonSizer.Add(CancelButton, 0, wx.ALIGN_LEFT)

        ButtonSizer.Add((140,30), 0)

        # Create OK button
        OKButton = wx.Button(self, wx.ID_OK)
        OKButton.SetDefault()
        ButtonSizer.Add(OKButton, 0, wx.ALIGN_RIGHT)

        ButtonSizer.Add((50,0),0)

        sizer.Add(ButtonSizer, 0, wx.ALIGN_CENTER_VERTICAL|wx.ALL|wx.EXPAND, 5)

        self.SetSizer(sizer)
        sizer.Fit(self)
        self.Raise()


class MyApp(wx.App):
    def OnInit(self):
        return True
        
    def MacOpenFile(self, filename):
        frame.Open(filename)


################################################################################
### MAIN LOOP OF THE APPLICATION                                             ###
################################################################################

##########
# Application-level Variables

Version = "beta 5"
Launch = True

# Initialize the library
GLOBAL.Library = CMLibrary()

app = MyApp()

frame = AppUI(None, wx.ID_ANY, 'Loop Analyst '+str(Version))
app.SetTopWindow(frame)

if len(argv) > 1:
    frame.Open(argv[1])

app.MainLoop()
