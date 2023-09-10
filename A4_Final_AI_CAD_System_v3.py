import os
import cv2  #Version: 3.4.2
import threading
import random
import shutil
import numpy as np   #Version: 1.21.5
import pandas as pd  #Version: 1.1.3
import pydicom       #Version: 2.3.0
#Pydicom  version: '2.3.0' #Version 1.3.0 cannot show ds.file_meta when only call ds
from pydicom.tag import Tag
import tkinter as tk       #Version 8.6.12
from tkinter import ttk
from tkinter import font
from tkinter import messagebox
import tensorflow as tf
from tensorflow import keras
from tensorflow.keras.models import load_model, Model
from matplotlib import pyplot, cm  #Version: 3.3.2
from PIL import Image, ImageTk     #Version: 9.0.1
#PACS Connection
import time
from pydicom.dataset import Dataset  #Version: 2.0.2
from pynetdicom import AE, evt, StoragePresentationContexts, debug_logger
from pynetdicom.sop_class import PatientRootQueryRetrieveInformationModelMove
#Pynetdicom : conda install is slow / pip install is faster loading data

#Version 3 Change 
#Optimize for-loop in pixel data and overlay data decoding

#Version 3 Change
#1. Connect PACS Server 
#(1) Delete Case.FilePathString Variable
#(2) Delete Case.FileName Label (Case.Patient: 22 labels to 21 labels)
#(3) Case.ImageName: DICOM File Name to DICOM Instance UID (Set SOPInstanceUID as Image_File_Name)
#(4) Change Patient_Instance Title to DICOM_Instance
#2. Deidentification: 25 labels to 20 labels
#(1) Delete Virtual_FileName, Real_FileName, DICOM_FileName, DICOM_Instance_Number / Add Virtual_DICOM_Name Label
#(2) Delete Virtual_MediaSOPInstanceUID, Real_MediaSOPInstanceUID Label(they are identical to SOPInstanceUID tag)
#(3) DeCSV file: Delete Patient_ID, Full_Image_Name  /  Change Image_File_Name from SOPInstanceUID to DIOCOM Flow Number 'F000001'  /  Set Patieent_Flow_Number and set it to the first column
#(4) Optimize Deidentificaiton work and working case by case
#3. Other Operation Change
#(1) Delete self.path_Crop_Finish variables and do not create 'Finish_Case_Crop' Folder anymore
#(2) Delete the 'Finish' Keyword in Check Operation
#(3) Save CSV Data after sorting 
#(4) Create Case.csv file when the first labeling work has been finished. (Version 2: Create the folder when the user fisrt review the case.)

"""
#path_OriginalDB='/Users/chulab/Desktop/USDBDemo/ANNA_FILE'
#path_Full_Image='/Users/chulab/Desktop/USDBDemo/US_Image_Only'
#path_Crop_Image='/Users/chulab/Desktop/USDBDemo/US_Crop_Image'
#path_Crop_Finish='/Users/chulab/Desktop/USDBDemo/Finish_Case_Temp'
"""

#Element Container
class Case:               #Case Object: the specific case data, the specific DICOM data, the specific ROI data
	def __init__(self):             #Called by Find_Action, __init__ Function(in MainWindow Class)
		#Case
		#self.FilePathString=''  #Case Folder Path                                                 #Setting: Find_file Function
		self.CSVPath=''         #Case CSV File Path                                               #Setting: Find_file Function
		#self.FileName=''        #Case Folder Name: var_FileName=eFileName.get()                   #Setting: Find_file Function 
		self.DICOM=[]           #DICOM Name List: DICOM_File (v3: DICOM Tag List [ds,ds,...])     #Setting: Find_file Function 
		self.CaseLabelData=''   #Case CSV Data(all): df                                           #Setting: Find_file Function / Resetting: Save_label

		#Image
		self.ImageName=''       #Present DICOM Name: var_ImageName                                #Setting: Input_image Function
		self.ImageNumber=0      #DICOM Name: image_number                                         #Setting: Find_file, Back, Next Function
		self.ImageArray=np.zeros((650,880,3),dtype=int)          #Image_array                     #Setting: Input_image Function
		self.ImageArraywithMask=np.zeros((650,880,3),dtype=int)  #Image_array_with_mask           #Setting: Input_image Function
		self.PatientID=''       #Var_PatientID                                                    #Setting: Input_image Function
		self.DICOMInstance=0    #DICOM Instance: Var_DICOMInstance                                #Setting: Input_image Function
		self.CSVDataItem=[]     #Case CSV Index for Image: df_item                                #Setting: Input_image Function / Resetting: Delete, set_Label_windows Function / Usage: Switch

		#ROI
		#self.Patient=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]
		self.Patient=[0,0,0,0, 0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]     #Setting: Switch, Save_label Function / Usage: Change_PInfo, Input_image, Delete, Crop, Clear_info, set_Label_windows Function
		self.ROIBoundary=[]     #ROI_Boundary                                                     #Setting: Input_image Function / Resetting: set_Label_windows Function / Usage: ROI, Switch, Delete, set_Label_windows Function
		self.USBoundary=[]      #US_Boundary                                                      #Setting: Input_image Function / Usage: Crop, set_Label_windows

class Database:           #Database Object: the database pathes
	def __init__(self):             #Called by __init__ Function(in MainWindow Class)
		self.path_OriginalDB = ''      #Setting: CreateFolders Function                                   #'/Users/chulab/Desktop/USDBDemo/ANNA_FILE'
		self.path_Full_Image = ''      #Setting: CreateFolders Function                                   #'/Users/chulab/Desktop/USDBDemo/US_Image_Only'
		self.path_Crop_Image = ''      #Setting: CreateFolders Function                                   #'/Users/chulab/Desktop/USDBDemo/US_Crop_Image'
		#self.path_Crop_Finish = ''     #Setting: CreateFolders Function                                   #'/Users/chulab/Desktop/USDBDemo/Finish_Case_Crop'
		self.path_Deidentify = ''      #Setting: CreateFolders Function / Create Folder: Deidentification #'/Users/chulab/Desktop/USDBDemo/Deidentification'
		self.path_AIModel=''           #Setting: CreateFolders Function                                   #'/Users/chulab/Desktop/USDBDemo/my_model.h5'

class MainPage:           #MainPage Object: the tkinter objects of the Main Window
	def __init__(self):
		#MainWindow Tkinter         #Setting: Main_Window_Show Function(in MainWindow Class)
		self.Window=''
		self.ImageFrame=''         #--ImageFrame--
		self.TopImageFrame=''      #--TopImageFrame--
		self.LeftTopImageFrame=''  #--LeftTopImageFrame--
		self.lFileName=''
		self.eFileName=''
		self.bFindFile=''
		self.bAddMarkup=''
		self.bRemoveROI=''
		self.lImageName1=''
		self.lImageName2=''
		self.bBack=''
		self.bNext=''
		self.RightTopImageFrame='' #--RightTopImageFrame--
		self.bAIClinic=''
		self.lROILocation=''
		#.............................................
		self.MiddleImageFrame=''   #--MiddleImageFrame--
		self.canvas=''
		self.photo=''              #Setting: Main_Window_Show/HeatMap_Action/Input_image/Find_file/Markup/Crop/Clear_info/set_Label_windows/HeatMap	
		self.ImageDcm=''
		self.rectangle1='' #2_Left / 1
		self.rectangle2='' #2_Right
		self.rectangle3='' #Label Usage
		#---------------------------------------------
		self.LabelFrame=''         #--LabelFrame--
		#.............................................
		self.TopLabelFrame=''      #--TopLabelFrame--
		self.lToolsDataBase=''
		self.bCheck=''
		self.bStatistics=''
		self.bDeidentify=''
		self.lToolsDicom=''
		self.bSwitch=''
		self.bLabel=''
		self.bDelete=''
		#.............................................
		self.MiddleLabelFrame=''   #--MiddleLabelFrame--
		self.lReport=''

		self.lPatient=''
		self.T_PID=''
		self.C_PID=''
		self.T_PFName=''
		self.C_PFName=''
		self.T_IFName=''
		self.C_IFName=''
		self.T_DCMIns=''  
		self.C_DCMIns=''  
		self.T_PFlow=''
		self.C_PFlow=''
			
		self.lOverAll=''
		self.T_USType=''
		self.C_USType=''
		self.T_BSide=''
		self.C_BSide=''
		self.T_BTissue=''
		self.C_BTissue=''

		self.lLesion='' 
		self.T_BIRADS=''
		self.C_BIRADS=''

		self.T_LSize=''   
		self.C_LSize=''   
		self.T_LDepth=''  
		self.C_LDepth='' 
		self.T_LLoca='' 
		self.C_LLoca=''  
			
		self.lFullImage=''
		self.T_FullSize=''
		self.C_FullSize=''
		self.T_FullPath=''
		self.C_FullPath='' 
	
		self.lROIImage=''
		self.T_ROILoca=''
		self.C_ROILoca=''
		self.T_ROISize=''
		self.C_ROISize=''

		self.lAIResult=''
		self.T_AIBirads=''
		self.C_AIBirads=''

		self.bHeatMap=''
		self.bAcceptResult=''

class LabelPage:          #LabelPage Object: the tkinter objects of the Label Window           
	def __init__(self):             #Called by __init__ Function(in Label Class)
		#Label_windows Tkinter      #Setting: Label_Window_Show Function(in Label Class)
		self.LabelWindows=''        
		self.EntryFrame=''       #---EntryFrame---
		self.lPatient=''
		self.T_FileName=''
		self.C_FileName=''
		self.T_DICOMFileName=''
		self.C_DICOMFileName=''
		self.LabelFrame=''       #---LabelFrame---
		self.lLabel='' 
		self.lItem1_r0c0=''      #---Breast Side---
		self.VarSide=''
		self.rRight=''
		self.rLeft=''
		self.lItem2_r1c0=''      #---Tissue Composition---
		self.VarTissue=''
		self.rFat=''
		self.rFibro=''
		self.rHet=''
		self.lItem3_r2c0=''      #---BI-RADS Level---
		self.VarBIRADS=''
		self.rC1=''
		self.rC2=''
		self.rC3=''
		self.rC4=''
		self.rC5=''
		self.lItem13_r0c4=''     #---Number of US---
		self.VarTypeUS=''
		self.rOne=''
		self.rLTwo=''
		self.rRTwo=''
		self.lItem10_r1c3=''     #---Lesion Location---
		self.VarLesionLocation=''
		self.rQI=''
		self.rQII=''
		self.rQIII=''
		self.rQIV=''
		self.lItem11_r2c3=''     #---Lesion Size(Max)---
		self.lScale_1=''
		self.sSize=''
		self.lItem12_r3c3=''     #---Lesion Depth---
		self.lScale_2=''
		self.sDepth=''
		self.bCropImage=''       #---Buttom---
		self.bSave=''
		self.bClear=''
		
		#Labeling Info
		self.X0=0                #the existed US data in CSV file (USBoundary: US Corner)(原始座標) #Setting: Crop Function 
		self.Y0=0
		self.X1=0
		self.Y1=0
		
		self.ROI_X0=0            #the present ROI info(原始座標)   #Setting: enter(event) Function 
		self.ROI_Y0=0
		self.ROI_W=0
		self.ROI_H=0
	
		self.refPt=[]            #the mouse info                   #Setting: enter(event) Function / Clearing: clear(event) Function

class CheckPage:          #CheckPage Object: the tkinter objects of the Check Window         
	def __init__(self):             #Called by __init__ Function(in Check Class)
		#Check_Report Tkinter       #Setting: Check_Window_Show Function(in Check Class)
		self.CheckWindows=''
		self.FullFrame=''
		self.CanvasFrame=''
		self.checkcanvas=''
		self.RightScrollbar=''
		
class StatisticsPage:	  #StatisticsPage Object: the tkinter objects of the Statistics Window            
	def __init__(self):	            #Called by __init__ Function(in Statistics Class)
		#Statistics Window Tkinter  #Setting: Statistics_Window_Show Function(in Statistics Class)
		self.StatisticsWindows=''
		self.ModeFrame=''         #---ModeFrame---
		self.ePatientName=''
		self.bCount=''
		self.lEmpty=''
		self.lFilter=''
		self.eBIRADS=''
		
		self.StatisticFrame=''    #---StatisticFrame---
		self.lStatisticsReport=''
		self.lCaseName=''
		self.lCountingCase=''
		self.lTatalImage=''
		self.lBIRADSFilter=''
		
		self.OverAll=''
		self.lBreastSide=''
		self.lLeft=''
		self.lRight=''
		
		self.lBreastTissue=''
		self.lFat=''
		self.lFibro=''
		self.lHetero=''
		
		self.lFullImage=''
		self.lBreastBIRADS=''
		self.lBIRADS2=''
		self.lBIRADS3=''
		self.lBIRADS4=''
		self.lBIRADS5=''
		
		self.lSize=''
		self.lSize1=''
		self.lSize2=''
		self.lSize3=''
		self.lSize4=''
		
		self.lDepth=''
		self.lDepth1=''
		self.lDepth2=''
		self.lDepth3=''
		self.lDepth4=''
		
		self.lROI=''
		self.lROIs128=''
		self.lROIs256=''
		self.lROImore=''
		
class Count:              #Count Object: the counting variables of show-up signs 
	def __init__(self):             #Called by Input_image Function(in Find Class), set_Label_windows Function(in Label Class)
		self.MarkupCount=0          #Setting: Markup Funtion
		self.ROICount=0             #Setting: ROI/Switch/Delete Funtion (Usage: ROI Funtion)
		self.SwitchCount=0          #Setting: Switch Funtion  (Usage: ROI/Switch/Delete Funtion)
		self.HeatmapCount=0         #Setting: HeatMap




#Action
class MainWindow:         #MainWindow Object: an action of Showing up the Main Window & Setting all of actions(main function)
	def __init__(self):
		Case.__init__(Case)
		Database.__init__(Database)
		Find.__init__(Find)
		Check.__init__(Check)
		Statistics.__init__(Statistics)
		#Deidentify.__init__(Deidentify)
		Label.__init__(Label)
	
	
	def Find_Action(self):          #Called by Main_Window_Show Function
		#Close Label Window if it exits
		if LabelPage.LabelWindows!='':    #LabelPage is open
			self.LabelObject.set_Label_windows()
		Case.__init__(Case)
		Find.Find_file(Find)                           #物件內容: 啟動Find按鈕的背後行為--找Case顯示DICOM
	
	def Back_Action(self):          #Called by Main_Window_Show Function
		#Close Label Window if it exits
		if LabelPage.LabelWindows!='':    #LabelPage is open
			self.LabelObject.set_Label_windows()
		#Do Back Button Action
		DCMControl.Back(DCMControl)
		
	def Next_Action(self):          #Called by Main_Window_Show Function
		#Close Label Window if it exits
		if LabelPage.LabelWindows!='':    #LabelPage is open
			self.LabelObject.set_Label_windows()
		#Do Next Button Action
		DCMControl.Next(DCMControl)
	
	def Markup_Action(self):        #Called by Main_Window_Show Function
		MarkControl.Markup(MarkControl)
	
	def ROI_Action(self):           #Called by Main_Window_Show Function
		MarkControl.ROI(MarkControl)
	
	
	def Check_Action(self):         #Called by Check_threading Function   #Version 2: No usage of threading
		if CheckPage.CheckWindows=='':
			self.CheckObject=Check()
			self.CheckObject.Missing_data_check()
			self.CheckObject.Check_Window_Show()
	
	def Check_threading(self):      #Called by Main_Window_Show Function  #Version 3: Data checking with PACS need time 
		task=threading.Thread(target = self.Check_Action)
		task.start()
	
	def Statistics_Action(self):    #Called by Main_Window_Show Function
		if StatisticsPage.StatisticsWindows=='':
			self.StatisObject=Statistics()
			self.StatisObject.find_csvfile_path_and_patientID_list(Database.path_OriginalDB)
			self.StatisObject.Statistics_Window_Show()
	
	def Deidentify_Action(self):    #Called by Deidentify_threading Function
		Deidentify.Deidentification(Deidentify)
		
	def Deidentify_threading(self): #Called by Main_Window_Show Function
		task=threading.Thread(target = self.Deidentify_Action)
		task.start()
	
	
	def Switch_Action(self):        #Called by Main_Window_Show Function
		MarkControl.Switch(MarkControl)

	def Delete_Action(self):        #Called by Main_Window_Show Function
		MarkControl.Delete(MarkControl)
	
	def Label_Action(self):         #Called by Main_Window_Show Function
		if LabelPage.LabelWindows=='':    #LabelPage is not open (only can open one LabelPage, can not open more than one LabelPage)
			self.LabelObject=Label()
			self.LabelObject.Label_Window_Show()
	
	
	def AIClinic_Action(self):      #Called by Main_Window_Show Function
		if LabelPage.LabelWindows!='':    #LabelPage is open
			AITool.AIClinic(AITool)
			AITool.HeatMap(AITool)
		elif LabelPage.LabelWindows=='':  #LabelPage is not open
			mWarning=messagebox.showwarning(title='Warning Window',message='Please change to the Label Mode first!', parent=MainPage.Window)
	
	def HeatMap_Action(self):       #Called by Main_Window_Show Function
		if LabelPage.LabelWindows!='':    #LabelPage is open
			Count.HeatmapCount=(Count.HeatmapCount+1)%2
			if Count.HeatmapCount==0: #with Grad_CAM
				img = Image.fromarray(AITool.Grad_CAM.astype(np.uint8),'RGB')
				MainPage.photo = ImageTk.PhotoImage(img)
				MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
			elif Count.HeatmapCount==1: #without Grad_CAM
				img = Image.fromarray(AITool.Original.astype(np.uint8),'RGB')
				MainPage.photo = ImageTk.PhotoImage(img)
				MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
			
		elif LabelPage.LabelWindows=='':  #LabelPage is not open
			mWarning=messagebox.showwarning(title='Warning Window',message='Please change to the Label Mode first!', parent=MainPage.Window)
			
	def Accept_Action(self):        #Called by Main_Window_Show Function
		if LabelPage.LabelWindows!='':    #LabelPage is open
			AITool.AcceptResult(AITool)
		elif LabelPage.LabelWindows=='':  #LabelPage is not open
			mWarning=messagebox.showwarning(title='Warning Window',message='Please change to the Label Mode first!', parent=MainPage.Window)
		
		
	def Main_Window_Show(self):     #Called by Main Function
		InitialSetting.CreateFolders(InitialSetting) #Setting DB Path
		#set main window-------------------------------------------------------------------------------------------------------------------------------------------
		MainPage.Window = tk.Tk()
		MainPage.Window.title('Ann\'s AI Window for Breast Sonography')
		MainPage.Window.geometry('1300x750')#uint:('widthxhight')
		MainPage.Window.resizable(0,0)

		#font decision
		f_title = font.Font(family="Helvetica", size=14, weight='bold')
		f_content1 = font.Font(family="Helvetica", size=14)
		f_content2 = font.Font(family="Helvetica", size=12, weight='bold')
		f_button1 = font.Font(family="Helvetica", size=12)
		f_button2 = font.Font(family="Helvetica", size=10)
		f_button3 = font.Font(family="Helvetica", size=12, weight='bold')
		f_button4 = font.Font(family="Helvetica", size=11)

		img = Image.fromarray(np.zeros((1,1),dtype=np.uint8),'L')
		MainPage.photo = ImageTk.PhotoImage(img)
		#---------------------------------------------
		MainPage.ImageFrame = tk.Frame(MainPage.Window)
		#.............................................
		MainPage.TopImageFrame = tk.Frame(MainPage.ImageFrame)

		MainPage.LeftTopImageFrame=tk.Frame(MainPage.TopImageFrame)
		MainPage.lFileName = tk.Label(MainPage.LeftTopImageFrame, text='Patient ID:',font=f_title, anchor='w').grid(row=0, column=0, columnspan=2, padx=5, pady=5, sticky='w') #Version 2: Case Name #Verison 3: Patient ID 
		MainPage.eFileName = tk.Entry(MainPage.LeftTopImageFrame,font=f_button1, show=None)
		MainPage.eFileName.grid(row=0, column=2, columnspan=3, padx=5, pady=5, sticky='w')
		MainPage.bFindFile = tk.Button(MainPage.LeftTopImageFrame, text='Find',font=f_button4, command=self.Find_Action)
		MainPage.bFindFile.grid(row=0, column=5, columnspan=1, padx=5, pady=5, sticky='w')
		MainPage.bAddMarkup = tk.Button(MainPage.LeftTopImageFrame, text='Markup',font=f_button4, command=self.Markup_Action)#
		MainPage.bAddMarkup.grid(row=0, column=8, columnspan=1, padx=5, pady=5, sticky='w')   
		#MainPage.bAddMarkup.grid(row=0, column=8, columnspan=1, padx=5, pady=5, sticky='e')
		MainPage.bRemoveROI = tk.Button(MainPage.LeftTopImageFrame, text='  ROI  ',font=f_button4, command=self.ROI_Action)#
		MainPage.bRemoveROI.grid(row=0, column=9, columnspan=1, padx=5, pady=5, sticky='w')
		#MainPage.bRemoveROI.grid(row=0, column=10, columnspan=1, padx=5, pady=5, sticky='w')

		MainPage.lImageName1 = tk.Label(MainPage.LeftTopImageFrame, text='DICOM Instance UID:' ,font=f_content2, anchor='w').grid(row=1, column=0, columnspan=3, padx=5, pady=5, sticky='w') #Version 3:  DICOM Instance UID, DICOM File Name #Version 2: Image File Name
		MainPage.lImageName2 = tk.Label(MainPage.LeftTopImageFrame, text='' ,font=f_button1, anchor='w')
		MainPage.lImageName2.grid(row=1, column=3, columnspan=7, padx=5, pady=5, sticky='w')
		#MainPage.lImageName2.grid(row=1, column=4, columnspan=3, padx=5, pady=5, sticky='w')
		MainPage.bBack = tk.Button(MainPage.LeftTopImageFrame, text='Back', font=f_button3, command=self.Back_Action)#
		MainPage.bBack.grid(row=0, column=6, columnspan=1, padx=5, pady=5,sticky='w')
		#MainPage.bBack.grid(row=0, column=12, columnspan=1, padx=5, pady=5,sticky='e')
		#MainPage.bBack.grid(row=1, column=8, columnspan=1, padx=5, pady=5,sticky='e')
		MainPage.bNext = tk.Button(MainPage.LeftTopImageFrame, text='Next', font=f_button3, command=self.Next_Action)#
		MainPage.bNext.grid(row=0, column=7, columnspan=1, padx=5, pady=5, sticky='w')
		#MainPage.bNext.grid(row=0, column=14, columnspan=1, padx=5, pady=5, sticky='w')
		#MainPage.bNext.grid(row=1, column=10, columnspan=1, padx=5, pady=5, sticky='w')
		MainPage.LeftTopImageFrame.pack(side='left', anchor='nw', expand='no')

		MainPage.RightTopImageFrame=tk.Frame(MainPage.TopImageFrame)
		MainPage.bAIClinic = tk.Button(MainPage.RightTopImageFrame, text='   AI Clinic   ',font=("Helvetica", 12, 'bold'), command=self.AIClinic_Action)#
		MainPage.bAIClinic.grid(row=0, column=13, columnspan=2, padx=5, pady=5, sticky='w')
		#MainPage.bAIClinic.pack(side='top', padx=10, pady=5, anchor='e', expand='no')
		MainPage.lROILocation = tk.Label(MainPage.RightTopImageFrame, text='' ,font=("Helvetica", 13))
		MainPage.lROILocation.grid(row=1, column=10, columnspan=5, padx=5, pady=5, sticky='w')
		#MainPage.lROILocation.pack(side='bottom', padx=10, pady=5, anchor='se', expand=True) 
		MainPage.RightTopImageFrame.pack(side='right', anchor='ne',fill='y', expand=True)

		MainPage.TopImageFrame.pack(side='top', anchor='ne', fill='both', expand='no')
		#.............................................
		MainPage.MiddleImageFrame=tk.Frame(MainPage.ImageFrame)
		MainPage.canvas = tk.Canvas(MainPage.MiddleImageFrame, height=650+20, width=880+20,bg='Gray')
		MainPage.canvas.pack()
		MainPage.ImageDcm = MainPage.canvas.create_image(10, 10, anchor='nw', image=MainPage.photo)
		MainPage.rectangle1 = MainPage.canvas.create_rectangle(10, 10, 10, 10, outline='white') #2_Left / 1
		MainPage.rectangle2 = MainPage.canvas.create_rectangle(10, 10, 10, 10, outline='white') #2_Right
		MainPage.rectangle3 = MainPage.canvas.create_rectangle(10, 10, 10, 10, outline='white') #Label Usage
		MainPage.MiddleImageFrame.pack(side='top', anchor='n', fill='both', expand='no')

		MainPage.ImageFrame.pack(side='left', anchor='nw', fill='y', expand='no')
		#---------------------------------------------
		MainPage.LabelFrame=tk.Frame(MainPage.Window)
		#.............................................
		MainPage.TopLabelFrame=tk.Frame(MainPage.LabelFrame)

		MainPage.lToolsDataBase = tk.Label(MainPage.TopLabelFrame, text='For the Database:', font=("Helvetica", 11, 'underline'), anchor='w').grid(row=0, column=0, columnspan=5, pady=5, sticky='w')
		MainPage.bCheck = tk.Button(MainPage.TopLabelFrame, text='  Check  ',font=f_button2, command=self.Check_threading)#Check_Action
		MainPage.bCheck.grid(row=0, column=6, columnspan=3, padx=5, pady=5, sticky='e')
		MainPage.bStatistics = tk.Button(MainPage.TopLabelFrame, text='Statistics',font=f_button2, command=self.Statistics_Action)#
		MainPage.bStatistics.grid(row=0, column=10, columnspan=3, padx=5, pady=5, sticky='e')
		MainPage.bDeidentify = tk.Button(MainPage.TopLabelFrame, text='Deidentify ',font=f_button2, command=self.Deidentify_threading)#
		MainPage.bDeidentify.grid(row=0, column=14, columnspan=3, padx=5, pady=5, sticky='e')

		MainPage.lToolsDicom = tk.Label(MainPage.TopLabelFrame, text='For this DICOM:', font=("Helvetica", 11, 'underline'), anchor='w').grid(row=1, column=0, columnspan=5, pady=5, sticky='w')
		MainPage.bSwitch = tk.Button(MainPage.TopLabelFrame, text='  Switch  ', font=f_button2, command=self.Switch_Action)#
		MainPage.bSwitch.grid(row=1, column=6, columnspan=3, padx=5, pady=5, sticky='e')	
		MainPage.bLabel = tk.Button(MainPage.TopLabelFrame, text='   Label   ', font=f_button2, command=self.Label_Action)#
		MainPage.bLabel.grid(row=1, column=10, columnspan=3, padx=5, pady=5, sticky='e')
		MainPage.bDelete = tk.Button(MainPage.TopLabelFrame, text='   Delete   ', font=f_button2, command=self.Delete_Action)#
		MainPage.bDelete.grid(row=1, column=14, columnspan=3, padx=5, pady=5, sticky='e')	

		MainPage.TopLabelFrame.pack(side='top', anchor='nw', fill='x', expand='no')
		#.............................................
		MainPage.MiddleLabelFrame=tk.Frame(MainPage.LabelFrame)
		MainPage.lReport = tk.Label(MainPage.MiddleLabelFrame, text='Patient Report', font=("Helvetica", 15, 'bold'), anchor='w').grid(row=0, column=0, columnspan=5, pady=3, sticky='w') 
		
		MainPage.lPatient = tk.Label(MainPage.MiddleLabelFrame, text='Patient', font=("Helvetica", 13, 'bold'), anchor='w').grid(row=1, column=0, columnspan=5, pady=2, sticky='w')
		MainPage.T_PID = tk.Label(MainPage.MiddleLabelFrame, text='Patient ID:', font=("Helvetica", 12), anchor='w')
		MainPage.T_PID.grid(row=2, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_PID = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_PID.grid(row=2, column=7, columnspan=8, padx=5, sticky='w')
		#MainPage.T_PFName = tk.Label(MainPage.MiddleLabelFrame, text='Patient File Name:', font=("Helvetica", 11), anchor='w')   #Version 3 : Cancel this item of patient report
		#MainPage.T_PFName.grid(row=3, column=2, columnspan=5, padx=5, sticky='w')
		#MainPage.C_PFName = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 11), anchor='w') #Previous Version: font 11, 12, 13
		#MainPage.C_PFName.grid(row=3, column=7, columnspan=8, padx=5, sticky='w')
		MainPage.T_IFName = tk.Label(MainPage.MiddleLabelFrame, text='DICOM Instance UID:', font=("Helvetica", 12), anchor='w')   #Version 3 : Image File Name -> DICOM Instance UID
		MainPage.T_IFName.grid(row=3, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_IFName = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_IFName.grid(row=3, column=7, columnspan=8, padx=5, sticky='w')
		MainPage.T_DCMIns = tk.Label(MainPage.MiddleLabelFrame, text='DICOM Instance:', font=("Helvetica", 12), anchor='w')
		MainPage.T_DCMIns.grid(row=4, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_DCMIns = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_DCMIns.grid(row=4, column=7, columnspan=8, padx=5, sticky='w')
		MainPage.T_PFlow = tk.Label(MainPage.MiddleLabelFrame, text='Patient Flow Number:', font=("Helvetica", 12), anchor='w')
		MainPage.T_PFlow.grid(row=5, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_PFlow = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_PFlow.grid(row=5, column=7, columnspan=8, padx=5, sticky='w')

		MainPage.lOverAll = tk.Label(MainPage.MiddleLabelFrame, text='Over All US Information', font=("Helvetica", 13, 'bold'), anchor='w').grid(row=6, column=0, columnspan=5, pady=2, sticky='w')
		MainPage.T_USType = tk.Label(MainPage.MiddleLabelFrame, text='Type of Ultrasound Image:', font=("Helvetica", 12), anchor='w')
		MainPage.T_USType.grid(row=7, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_USType = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_USType.grid(row=7, column=7, columnspan=8, padx=5, sticky='w')
		MainPage.T_BSide = tk.Label(MainPage.MiddleLabelFrame, text='Breast Side:', font=("Helvetica", 12), anchor='w')
		MainPage.T_BSide.grid(row=8, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_BSide = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_BSide.grid(row=8, column=7, columnspan=8, padx=5, sticky='w')
		MainPage.T_BTissue = tk.Label(MainPage.MiddleLabelFrame, text='Tissue Composition:', font=("Helvetica", 12), anchor='w')
		MainPage.T_BTissue.grid(row=9, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_BTissue = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_BTissue.grid(row=9, column=7, columnspan=8, padx=5, sticky='w')

		MainPage.lLesion = tk.Label(MainPage.MiddleLabelFrame, text='US Lesion Feature', font=("Helvetica", 13, 'bold'), anchor='w').grid(row=10, column=0, columnspan=5, pady=2, sticky='w')
		MainPage.T_BIRADS = tk.Label(MainPage.MiddleLabelFrame, text='BI-RADS Level:', font=("Helvetica", 12), anchor='w')
		MainPage.T_BIRADS.grid(row=11, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_BIRADS = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_BIRADS.grid(row=11, column=7, columnspan=8, padx=5, sticky='w')

		MainPage.T_LSize = tk.Label(MainPage.MiddleLabelFrame, text='Lesion Size(Max):', font=("Helvetica", 12), anchor='w')
		MainPage.T_LSize.grid(row=12, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_LSize = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_LSize.grid(row=12, column=7, columnspan=8, padx=5, sticky='w')
		MainPage.T_LDepth = tk.Label(MainPage.MiddleLabelFrame, text='Lesion Depth:', font=("Helvetica", 12), anchor='w')
		MainPage.T_LDepth.grid(row=13, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_LDepth = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_LDepth.grid(row=13, column=7, columnspan=8, padx=5, sticky='w')
		MainPage.T_LLoca = tk.Label(MainPage.MiddleLabelFrame, text='Lesion Location:', font=("Helvetica", 12), anchor='w')
		MainPage.T_LLoca.grid(row=14, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_LLoca = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_LLoca.grid(row=14, column=7, columnspan=8, padx=5, sticky='w')

		MainPage.lFullImage = tk.Label(MainPage.MiddleLabelFrame, text='Full Image Info', font=("Helvetica", 13, 'bold'), anchor='w').grid(row=15, column=0, columnspan=5, pady=2, sticky='w')
		MainPage.T_FullSize = tk.Label(MainPage.MiddleLabelFrame, text='Full Image Size:', font=("Helvetica", 12), anchor='w')
		MainPage.T_FullSize.grid(row=16, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_FullSize = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_FullSize.grid(row=16, column=7, columnspan=8, padx=5, sticky='w')
		MainPage.T_FullPath = tk.Label(MainPage.MiddleLabelFrame, text='Full Image Path:', font=("Helvetica", 12), anchor='w')
		MainPage.T_FullPath.grid(row=17, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_FullPath = tk.Label(MainPage.MiddleLabelFrame, text='.../US_Image_Only/0', font=("Helvetica", 12), anchor='w')
		MainPage.C_FullPath.grid(row=18, column=2, columnspan=15, padx=5, sticky='w')
			
		MainPage.lROIImage = tk.Label(MainPage.MiddleLabelFrame, text='ROI Image Info', font=("Helvetica", 13, 'bold'), anchor='w').grid(row=19, column=0, columnspan=5, pady=2, sticky='w')
		MainPage.T_ROILoca= tk.Label(MainPage.MiddleLabelFrame, text='ROI Start Location:', font=("Helvetica", 12), anchor='w')
		MainPage.T_ROILoca.grid(row=20, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_ROILoca = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_ROILoca.grid(row=20, column=7, columnspan=8, padx=5, sticky='w')
		MainPage.T_ROISize = tk.Label(MainPage.MiddleLabelFrame, text='ROI Image Size:', font=("Helvetica", 12), anchor='w')
		MainPage.T_ROISize.grid(row=21, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_ROISize = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_ROISize.grid(row=21, column=7, columnspan=8, padx=5, sticky='w')

		MainPage.lAIResult = tk.Label(MainPage.MiddleLabelFrame, text='AI Clinic Result', font=("Helvetica", 13, 'bold'), anchor='w').grid(row=22, column=0, columnspan=5, pady=2, sticky='w')
		MainPage.T_AIBirads = tk.Label(MainPage.MiddleLabelFrame, text='AI BI-RADS Level:', font=("Helvetica", 12), anchor='w')
		MainPage.T_AIBirads.grid(row=23, column=2, columnspan=5, padx=5, sticky='w')
		MainPage.C_AIBirads = tk.Label(MainPage.MiddleLabelFrame, text='0', font=("Helvetica", 12), anchor='w')
		MainPage.C_AIBirads.grid(row=23, column=7, columnspan=8, padx=5, sticky='w')

		MainPage.bHeatMap = tk.Button(MainPage.MiddleLabelFrame, text=' Heat Map ',font=("Helvetica", 13, 'bold'), command=self.HeatMap_Action)#
		MainPage.bHeatMap.grid(row=24, column=7, columnspan=3, padx=5, pady=7, sticky='w')	
		MainPage.bAcceptResult = tk.Button(MainPage.MiddleLabelFrame, text=' Accept ',font=("Helvetica", 13, 'bold'), command=self.Accept_Action)#
		MainPage.bAcceptResult.grid(row=24, column=10, columnspan=5, padx=5, pady=7, sticky='w')	

		MainPage.MiddleLabelFrame.pack(side='top', anchor='n', fill='both', expand='no')
		MainPage.LabelFrame.pack(side='right', anchor='nw', fill='y', expand='yes')
		MainPage.Window.mainloop()


class InitialSetting:     #InitialSetting Object: an action of Checking DB Folders
	def __init__(self):
		pass
		
	def CreateFolders(self):        #Called by Main_Window_Show Function(in MainWindow Class)
		#Code Folder Path: 
		PresentPath = os.getcwd() #This program path(此程式檔案所在地)           #'/Users/chulab/Desktop/MNIST_coding/A4_Final_AI_CAD_System/Final System Code'
        #Folder Path: [Anns AI Windows]       
		RootPath = os.path.join(os.path.dirname(PresentPath), 'Anns AI Windows') #'/Users/chulab/Desktop/MNIST_coding/A4_Final_AI_CAD_System/Anns AI Windows'
		if not os.path.exists(RootPath):
			os.mkdir(RootPath)
		#Folder Path: [ANNA_FILE]	
		Database.path_OriginalDB = os.path.join(RootPath, 'ANNA_FILE')           #'/Users/chulab/Desktop/MNIST_coding/A4_Final_AI_CAD_System/Anns AI Windows/ANNA_FILE'
		if not os.path.exists(Database.path_OriginalDB):
			os.mkdir(Database.path_OriginalDB)
		#Folder Path: [US_Image_Only]	
		Database.path_Full_Image = os.path.join(RootPath, 'US_Image_Only')       #'/Users/chulab/Desktop/MNIST_coding/A4_Final_AI_CAD_System/Anns AI Windows/US_Image_Only'
		if not os.path.exists(Database.path_Full_Image):
			os.mkdir(Database.path_Full_Image)
		#Folder Path: [US_Crop_Image]	
		Database.path_Crop_Image = os.path.join(RootPath, 'US_Crop_Image')       #'/Users/chulab/Desktop/MNIST_coding/A4_Final_AI_CAD_System/Anns AI Windows/US_Crop_Image'
		if not os.path.exists(Database.path_Crop_Image):
			os.mkdir(Database.path_Crop_Image)
		#Folder Path: [Deidentification]
		Database.path_Deidentify = os.path.join(RootPath, 'Deidentification')    #'/Users/chulab/Desktop/MNIST_coding/A4_Final_AI_CAD_System/Anns AI Windows/Deidentification'
		if not os.path.exists(Database.path_Deidentify):
			os.mkdir(Database.path_Deidentify)
		#File Path: [my_model.h5]
		Database.path_AIModel = os.path.join(PresentPath, 'my_model.h5')         #'/Users/chulab/Desktop/MNIST_coding/A4_Final_AI_CAD_System/Final System Code/my_model.h5'
		
			
class Find:               #Find Object: an action of Find button
	def __init__(self):                                        #Called by __init__ Function(in MainWindow Class)
		#[self.Groups Info]:
		#Patient Info: 4 (DICOM: 2)
		#US Description: 3
		#Lesion Feature: 10
		#ROI Description: 4
		#Find_file #Version 3: Remove Patient_File_Name 
		self.Groups=["Patient_ID", "Image_File_Name", "DICOM_Instance", "Patient_Flow_Number", 
			"Ultrasound_Number", "Breast_Side", "Tissue_Composition", "BIRADS_Level",
			"Mass_Shape", "Mass_Margin", "Mass_Orientation", "Echo_Pattern", "Posterior_Feature", 
			"Calcification", "Mass_Size", "Lesion_Depth", "Lesion_Location",
			"Full_Size","Full_Image_Path","ROI_Start_Location","ROI_Image_Size"] 
		
	def get_colon_location_in_a_string(self, var_String):    #Called by Input_image Function(in Find Class), set_Label_windows Function(in Label Class)     #input a string / return two numbers (XY or WH)
		colon_loca_list=[] #colon(:) locations 
		var_1=0            
		var_2=0
		for i in range(0,len(var_String)): #Run through all characters to find two colons in a string
			if var_String[i]==':':
				colon_loca_list=colon_loca_list+[int(i)]
		var_1=int(var_String[colon_loca_list[0]+1:colon_loca_list[1]-1])
		var_2=int(var_String[colon_loca_list[1]+1:])
		return var_1,var_2 
	
	def Change_PInfo(self, Patient):                         #Called by Input_image, Find_file Function(in Find Class), Switch, Delete Function(in MarkControl Class), Crop, Save_label, Clear_info, set_Label_windows Function(in Label Class)
		MainPage.C_PID.config(text=Patient[0])
		if Patient[1]==0:                          #Version 3 : Remove Patient_File_Name item and Change Image_File_Name to DICOM InstaneUID 
			MainPage.C_IFName.config(text=Patient[1])
		else:
			MainPage.C_IFName.config(text=Patient[1][0:11]+'...'+Patient[1][-6:])
		MainPage.C_DCMIns.config(text=Patient[2])
		MainPage.C_PFlow.config(text=Patient[3])
		
		MainPage.C_USType.config(text=Patient[4])
		MainPage.C_BSide.config(text=Patient[5])
		MainPage.C_BTissue.config(text=Patient[6])
		
		MainPage.C_BIRADS.config(text=Patient[7])
		MainPage.C_LSize.config(text=Patient[14])
		MainPage.C_LDepth.config(text=Patient[15])
		MainPage.C_LLoca.config(text=Patient[16])
		
		MainPage.C_FullSize.config(text=Patient[17])
		#MainPage.C_FullPath.config(text='...'+Patient[19][75:])                    #Version 2: 32, 32+43
		MainPage.C_FullPath.config(text='...'+Patient[18][89:130]+'...')            #Version 3: 32+43+14+11+30 (InstanceUID)
		MainPage.C_ROILoca.config(text=Patient[19])
		MainPage.C_ROISize.config(text=Patient[20])
	
	def Input_image(self, ImageNumber):                      #Called by Find_file Function(in MainWindow Class), Back, Next Function(in DCMControl Class)
		#Case.Patient=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]
		Case.Patient=[0,0,0,0, 0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]
		self.Change_PInfo(self, Case.Patient)
		
		#Initialize Count
		Count.__init__(Count)
		
		#canvas
		MainPage.canvas.coords(MainPage.rectangle1,(10, 10, 10, 10)) #2_Left / 1
		MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10)) #2_Right
		MainPage.canvas.coords(MainPage.rectangle3,(10, 10, 10, 10)) #Label

		#Set var_ImageName
		Case.ImageName=str(Case.DICOM[ImageNumber].SOPInstanceUID)          #Version 3: Unique Instance UID(A DICOM File)
		#Case.ImageName='F'+'0'*(6-len(str(ImageNumber)))+str(ImageNumber)  #Version 2: DICOM Flow Name
		MainPage.lImageName2.config(text=Case.ImageName)
		#Set OpenDCM_path
		#OpenDCM_path=os.path.join(Case.FilePathString,Case.ImageName)
		
		#Get dicom info
		#ds = pydicom.dcmread(OpenDCM_path)        #Version 2: Read DICOM File with path
		ds = Case.DICOM[ImageNumber]               #Version 3: Choose the DICOM tag sent by PACS 
		#Case.PatientID=ds.PatientID               #ds.PatientID type:<class 'str'>                #Version 3: Case.PatientID is set by Find.Find_file function	/ Case.PatientID = MainPage.eFileName.get()	 
		Case.DICOMInstance=int(ds.InstanceNumber)  #ds.InstanceNumber type(version: 1.3.0): <class 'pydicom.valuerep.IS'>
		
		#Image_array
		DicomPixel_array=ds.pixel_array
		if DicomPixel_array.shape==(650,880,3):
			Case.ImageArray = DicomPixel_array
			#Gray scale picture: three channels are same value
		elif DicomPixel_array.shape==(650,880):	
			Case.ImageArray = cv2.merge([DicomPixel_array, DicomPixel_array, DicomPixel_array])  #Version 3: Faster algorithm 

				
		#annotation	(cartoon)
		rows = ds[0x0028, 0x0010].value #00280010 US rows/60040010 Overlay rows
		cols = ds[0x0028, 0x0011].value	
		annotation=np.zeros((650,880),dtype=int)
		if Tag(0x60043000) in ds:
			overlay_data = ds[0x60043000].value
			# read data from buffer
			annotation = np.frombuffer(overlay_data, dtype=np.uint8)
			annotation = np.unpackbits(annotation)
			# truncate padded values
			annotation = annotation[:rows*cols]
			# reshape and swap the byte order by hand
			annotation = np.reshape(annotation, (-1, 8))
			annotation = np.fliplr(annotation)
			annotation = np.reshape(annotation, (rows, cols))
		#markup (left down+markup)
		markup=np.zeros((650,880),dtype=int)
		if Tag(0x60003000) in ds:
			overlay_data = ds[0x60003000].value
			# read data from buffer
			markup = np.frombuffer(overlay_data, dtype=np.uint8)
			markup = np.unpackbits(markup)
			# truncate padded values
			markup = markup[:rows*cols]
			# reshape and swap the byte order by hand
			markup = np.reshape(markup, (-1, 8))
			markup = np.fliplr(markup)
			markup = np.reshape(markup, (rows, cols))	
		#Mask (annotation + markup)  #Version 2: Faster algorithm 
		Mask = np.zeros((650,880,1),dtype=int)
		Mask[markup[:,:]==1]=255
		Mask[annotation[:,:]==1]=255
		Mask = cv2.merge([Mask, Mask, Mask])
		#Image_array_with_mask    #Version 2: Faster algorithm 
		Case.ImageArraywithMask=Mask+Case.ImageArray
		Case.ImageArraywithMask[Case.ImageArraywithMask[:,:,:]>255]=255
		
		#Set US ROI Bounding
		Case.USBoundary=[]  #[[X0,Y0,X1,Y1]]
		image_element = ds.SequenceOfUltrasoundRegions
		for i in range(0,len(list(image_element))):
			if image_element[i][0x00186014].value==1 and image_element[i][0x00186016].value==2:  #(0018,6014): Region Data Type / (0018,6016): Region Flags
				X0=image_element[i][0x00186018].value #(0018,6018): Region Location Min X0 
				Y0=image_element[i][0x0018601A].value #(0018,601A): Region Location Min Y0
				X1=image_element[i][0x0018601C].value #(0018,601C): Region Location Max X1
				Y1=image_element[i][0x0018601E].value #(0018,601E): Region Location Max Y1
				Case.USBoundary += [[X0,Y0,X1,Y1]]
		#Sorting
		Case.USBoundary.sort() #a specific US (X0, Y0) 左上座標
		
		#decode CSV get roi data
		Case.CSVDataItem=[]
		ROI_X0_L, ROI_Y0_L, ROI_Weight_L, ROI_Height_L = 0, 0, 0, 0
		ROI_X0_R, ROI_Y0_R, ROI_Weight_R, ROI_Height_R = 0, 0, 0, 0
		for i in range(0,len(Case.CaseLabelData)):
			if str(Case.CaseLabelData['Image_File_Name'][i])==str(Case.ImageName):
				if str(Case.CaseLabelData['Ultrasound_Number'][i])=='2_Left' or str(Case.CaseLabelData['Ultrasound_Number'][i])=='1':
					ROI_X0_L,ROI_Y0_L = self.get_colon_location_in_a_string(self, str(Case.CaseLabelData['ROI_Start_Location'][i]))
					ROI_Weight_L,ROI_Height_L = self.get_colon_location_in_a_string(self, str(Case.CaseLabelData['ROI_Image_Size'][i]))
					
				elif str(Case.CaseLabelData['Ultrasound_Number'][i])=='2_Right':
					ROI_X0_R,ROI_Y0_R = self.get_colon_location_in_a_string(self, str(Case.CaseLabelData['ROI_Start_Location'][i]))
					ROI_Weight_R,ROI_Height_R = self.get_colon_location_in_a_string(self, str(Case.CaseLabelData['ROI_Image_Size'][i]))	

				Case.CSVDataItem=Case.CSVDataItem+[i]
		
		
		#ROI_Boundary & showup ROI Defloat
		Case.ROIBoundary=[]
		if len(Case.USBoundary)==1:
			Case.ROIBoundary=Case.ROIBoundary+[[int(ROI_X0_L+Case.USBoundary[0][0]),int(ROI_Y0_L+Case.USBoundary[0][1]),int(ROI_Weight_L),int(ROI_Height_L)]] #[DICOM X 座標, DICOM Y 座標, ROI Weight, ROI Height]
		elif len(Case.USBoundary)==2:
			if ROI_X0_L!=0 or ROI_Y0_L!=0 or ROI_Weight_L!=0 or ROI_Height_L!=0:
				Case.ROIBoundary=Case.ROIBoundary+[[int(ROI_X0_L+Case.USBoundary[0][0]),int(ROI_Y0_L+Case.USBoundary[0][1]),int(ROI_Weight_L),int(ROI_Height_L)]]
			if ROI_X0_R!=0 or ROI_Y0_R!=0 or ROI_Weight_R!=0 or ROI_Height_R!=0:
				Case.ROIBoundary=Case.ROIBoundary+[[int(ROI_X0_R+Case.USBoundary[1][0]),int(ROI_Y0_R+Case.USBoundary[1][1]),int(ROI_Weight_R),int(ROI_Height_R)]]
		
		if len(Case.ROIBoundary)==1:
			MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3])) #rectangle1: 1 or 2_Left
			MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10))		
		elif len(Case.ROIBoundary)==2:	
			MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3]))
			MainPage.canvas.coords(MainPage.rectangle2,(10+Case.ROIBoundary[1][0], 10+Case.ROIBoundary[1][1], 10+Case.ROIBoundary[1][0]+Case.ROIBoundary[1][2], 10+Case.ROIBoundary[1][1]+Case.ROIBoundary[1][3])) #rectangle1: 2_Right
		
		#showup Image Defloat
		MainPage.canvas.config(height=650+20, width=880+20)
		img = Image.fromarray(Case.ImageArraywithMask.astype(np.uint8),'RGB')
		MainPage.photo = ImageTk.PhotoImage(img)
		MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
	
	"""
	def PACS_dicom_return(self, PID, Mode):                    #Called by Find_file, Missing_data_check(in Check Class) Function  #Mode: 'InstanceUID', 'DICOM'
		self.DataList = []  #PACS Return Data
		
		def handle_store(event):                               #Called by PACS_dicom_return Function
			#Handle a C-STORE service request
			# Nothing fancy, just write to DICOM File Format
			ds = event.dataset
			ds.file_meta = event.file_meta
			#print(ds)
			#time.sleep(3)
			#Case.DICOM += [ds]
			if Mode =='DICOM':
				self.DataList+=[ds]
				#Case.DICOM += [ds]
			elif Mode =='InstanceUID':
				self.DataList+=[ds.SOPInstanceUID]
			#print(PID)
			return 0x0000
		
		# Bind our C-STORE handler
		#handlers = [(evt.EVT_C_STORE, handle_store)]
		handlers = [(evt.EVT_C_STORE, handle_store)]

		# Initialise the Application Entity
		ae = AE()
		ae.add_requested_context(PatientRootQueryRetrieveInformationModelMove)
		ae.supported_contexts = StoragePresentationContexts

		# Start our Storage SCP in non-blocking mode, listening on port 11120
		ae.ae_title = b'AICADSYSTEM'
		scp = ae.start_server(('127.0.0.1', 11114), block=False, evt_handlers=handlers)

		# Create out identifier (query) dataset
		# Fill out your query as appropriate
		ds = Dataset()
		#ds.QueryRetrieveLevel = 'PATIENT'
		ds.PatientID = str(PID)
		#ds.StudyInstanceUID = '1.2.826.0.1.3680043.2.77.83.20190817115618281.392'    #Unique Study UID(A Study of DICOM Files)
		#ds.SeriesInstanceUID = '1.2.826.0.1.3680043.2.77.83.20190817115618281.392.1' #Unique Series UID(A Series of DICOM Files)
		#ds.SOPInstanceUID='1.2.826.0.1.3680043.2.77.83.20191127145328586.5016.1'      #Unique Instance UID(A DICOM File)


		# Associate with peer AE at IP 127.0.0.1 and port 4242
		assoc = ae.associate('127.0.0.1', 4242)

		if assoc.is_established:
			# Use the C-MOVE service to send the identifier
			responses = assoc.send_c_move(ds, b'AICADSYSTEM', PatientRootQueryRetrieveInformationModelMove)

			for (status, identifier) in responses:
				if status:
					print('C-MOVE query status: 0x{0:04x}'.format(status.Status))
				else:
					print('Connection timed out, was aborted or received invalid response')

			# Release the association
			assoc.release()
		else:
			print('Association rejected, aborted or never connected')

		# Stop our Storage SCP
		scp.shutdown()
		#print(self.DataList)
		return self.DataList
		"""
		
	def PACS_dicom_return(self, PID):       #Version 3 : Get DICOMs from PACS        #Called by Find_file, Missing_data_check(in Check Class), Deidentification(in Deidentify Class) Function  #Return InstanceUIDList, DICOMDataList
		self.InstanceUIDList = []   #PACS Return Data
		self.DICOMDataList = []     #PACS Return Data
		
		def handle_store(event):                                                     #Called by PACS_dicom_return Function
			#Handle a C-STORE service request
			ds = event.dataset
			ds.file_meta = event.file_meta
			
			self.InstanceUIDList += [ds.SOPInstanceUID]  #DICOM InstanceUID Tag
			self.DICOMDataList += [ds]                   #DICOM Data
			return 0x0000
		
		# Bind our C-STORE handler
		#handlers = [(evt.EVT_C_STORE, handle_store)]
		handlers = [(evt.EVT_C_STORE, handle_store)]

		# Initialise the Application Entity
		ae = AE()
		ae.add_requested_context(PatientRootQueryRetrieveInformationModelMove)
		ae.supported_contexts = StoragePresentationContexts

		# Start our Storage SCP in non-blocking mode, listening on port 11120
		ae.ae_title = b'AICADSYSTEM'
		scp = ae.start_server(('127.0.0.1', 11114), block=False, evt_handlers=handlers)

		# Create out identifier (query) dataset
		# Fill out your query as appropriate
		ds = Dataset()
		#ds.QueryRetrieveLevel = 'PATIENT'
		ds.PatientID = str(PID)
		#ds.StudyInstanceUID = '1.2.826.0.1.3680043.2.77.83.20190817115618281.392'    #Unique Study UID(A Study of DICOM Files)
		#ds.SeriesInstanceUID = '1.2.826.0.1.3680043.2.77.83.20190817115618281.392.1' #Unique Series UID(A Series of DICOM Files)
		#ds.SOPInstanceUID='1.2.826.0.1.3680043.2.77.83.20191127145328586.5016.1'      #Unique Instance UID(A DICOM File)


		# Associate with peer AE at IP 127.0.0.1 and port 4242
		assoc = ae.associate('127.0.0.1', 4242)

		if assoc.is_established:
			# Use the C-MOVE service to send the identifier
			responses = assoc.send_c_move(ds, b'AICADSYSTEM', PatientRootQueryRetrieveInformationModelMove)

			for (status, identifier) in responses:
				if status:
					print('C-MOVE query status: 0x{0:04x}'.format(status.Status))
				else:
					print('Connection timed out, was aborted or received invalid response')

			# Release the association
			assoc.release()
		else:
			print('Association rejected, aborted or never connected')

		# Stop our Storage SCP
		scp.shutdown()

		return self.InstanceUIDList, self.DICOMDataList
	
	def Find_file(self):                                       #Called by Find_Action Function(in MainWindow Class)
		Case.PatientID = MainPage.eFileName.get()              #Setting Case.PatientID  #Version 3: Input Patient ID to get DICOMs in PACS & Delete Case.FileName item 
		#patient file/csv file path Setting
		Case.CSVPath = os.path.join(Database.path_OriginalDB, Case.PatientID+'.csv')

		#Get DICOM Data                            #Version 3: Get DICOMs from PACS Server
		_, Case.DICOM = self.PACS_dicom_return(self, str(Case.PatientID))
		#Case.DICOM = self.PACS_dicom_return(self, str(Case.FileName), 'DICOM') #Previous PACS_dicom_return function
		
		#Check the input Patient ID is correct and the PACS has sent the data to our AE (& Create CSV path) #Version 3: Cheak Case.DICOM is not empty.
		if len(Case.DICOM)==0: 
			#Initialize MainWindow(Clear)
			MainPage.lImageName2.config(text='')                        #Reset MainPage DICOM File Name
			img = Image.fromarray(np.zeros((1,1),dtype=np.uint8),'L')   #Reset MainPage Canvas
			MainPage.photo = ImageTk.PhotoImage(img)
			MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
			MainPage.canvas.coords(MainPage.rectangle1,(10, 10, 10, 10)) #2_Left / 1
			MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10)) #2_Right
			MainPage.canvas.coords(MainPage.rectangle3,(10, 10, 10, 10)) #Label
			Case.Patient=[0,0,0,0, 0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]     #Reset MainPage Patient Report(Version 3)
			#Case.Patient=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]     #Reset MainPage Patient Report
			self.Change_PInfo(self, Case.Patient)
			mWarning=messagebox.showwarning(title='Warning Window',message='Please input a correct Case Name!')
			return
		#elif not os.path.exists(Case.CSVPath):    #Version 3: Don't create empty CSV File untill the first label work is finished.
			#df=pd.DataFrame([], columns=self.Groups)
			#df.to_csv(Case.CSVPath, mode='w', header=True, index=False)
		
		#Patient CSV file information Setting	   #Open Patient CSV
		#Case.CaseLabelData = pd.read_csv(Case.CSVPath)
		#Case.CaseLabelData = Case.CaseLabelData.sort_values(by=['Image_File_Name','Ultrasound_Number'], ascending=True, ignore_index=True)
		
		#Patient CSV file information Setting     #Version 3: If Patient CSV exist, open the patient CSV
		if os.path.exists(Case.CSVPath):
			Case.CaseLabelData = pd.read_csv(Case.CSVPath)
			Case.CaseLabelData = Case.CaseLabelData.sort_values(by=['Image_File_Name','Ultrasound_Number'], ascending=True, ignore_index=True)
		
		#Patient information initial Setting
		Case.ImageNumber=0
		self.Input_image(self, Case.ImageNumber)
		

class MarkControl:        #MarkControl Object: an action of Markup, ROI, Switch, Delete button
	def __init__(self):
		pass
		
	def Markup(self):                #Called by Markup_Action Function(in MainWindow Class) 
		Count.MarkupCount=(Count.MarkupCount+1)%2
		#showup Image
		MainPage.canvas.config(height=650+20, width=880+20)
		if Count.MarkupCount==0: #with Markup
			img = Image.fromarray(Case.ImageArraywithMask.astype(np.uint8),'RGB')
		elif Count.MarkupCount==1: #without Markup
			img = Image.fromarray(Case.ImageArray.astype(np.uint8),'RGB')
		MainPage.photo = ImageTk.PhotoImage(img)
		MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
	
	def ROI(self):                   #Called by ROI_Action Function(in MainWindow Class) 
		Count.ROICount=(Count.ROICount+1)%2
		if Count.ROICount==0: #show up ROI 
			if len(Case.ROIBoundary)==0:	#there is not any ROI Boundary information in this DICOM 
				MainPage.canvas.coords(MainPage.rectangle1,(10, 10, 10, 10))
				MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10))
			elif len(Case.ROIBoundary)==1:  #there is only one ROI Boundary information in this DICOM (1 or 2_Left or 2_Right (only one side)) 
				MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3]))
				MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10))
			elif len(Case.ROIBoundary)==2:  #there is two ROI Boundary informations in this DICOM (2_Left and 2_Right) 
				if Count.SwitchCount==0:  #show up 2 sides ROI 
					MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3]))#rectangle1(first usage): 1 or 2_Left or only one side
					MainPage.canvas.coords(MainPage.rectangle2,(10+Case.ROIBoundary[1][0], 10+Case.ROIBoundary[1][1], 10+Case.ROIBoundary[1][0]+Case.ROIBoundary[1][2], 10+Case.ROIBoundary[1][1]+Case.ROIBoundary[1][3]))#rectangle1(secound usage): 2_Right (in two sides ROI)
				elif Count.SwitchCount==1: #show up Left side ROI 
					MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3]))
					MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10))
				elif Count.SwitchCount==2: #show up Right side ROI 
					MainPage.canvas.coords(MainPage.rectangle1,(10, 10, 10, 10))
					MainPage.canvas.coords(MainPage.rectangle2,(10+Case.ROIBoundary[1][0], 10+Case.ROIBoundary[1][1], 10+Case.ROIBoundary[1][0]+Case.ROIBoundary[1][2], 10+Case.ROIBoundary[1][1]+Case.ROIBoundary[1][3]))
		elif Count.ROICount==1: #not show up ROI
			MainPage.canvas.coords(MainPage.rectangle1,(10, 10, 10, 10))
			MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10))
	
	def Switch(self):                #Called by Switch_Action Function(in MainWindow Class) 
		#Check if LabelPage.LabelWindows exist (Ask a question)(Version 3)
		if LabelPage.LabelWindows!='' and len(Case.CSVDataItem) != 0:
			MsgBox = messagebox.askquestion ('The Label Window is open!','Do you want to view the previous data ?',icon = 'warning')
			print('Switch MsgBox:', MsgBox)
			if MsgBox == 'no': #(if the answer is no, the program doesn't run the switch code.)
				return
			
		#Check the CSV file exists
		if Case.CaseLabelData.empty or len(Case.CSVDataItem) == 0 or len(Case.ROIBoundary) == 0:
			mWarning=messagebox.showwarning(title='Warning Window',message='There isn\'t any ROI data!')
			return 
		
		#Switch_count Setting
		Count.ROICount=0
		if len(Case.CSVDataItem) == 1:
			Count.SwitchCount=(Count.SwitchCount+1)%2
			#self.SwitchCount=1
		elif len(Case.CSVDataItem) == 2:
			Count.SwitchCount=(Count.SwitchCount+1)%3
		#print('Switch_count:', self.SwitchCount)	
		#Operation	
		if Count.SwitchCount==0: #Initial
			#Case.Patient=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]
			Case.Patient=[0,0,0,0, 0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]  #Version 3
			if len(Case.CSVDataItem) == 1:
				MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3]))
				MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10))
			elif len(Case.CSVDataItem) == 2:
				MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3]))
				MainPage.canvas.coords(MainPage.rectangle2,(10+Case.ROIBoundary[1][0], 10+Case.ROIBoundary[1][1], 10+Case.ROIBoundary[1][0]+Case.ROIBoundary[1][2], 10+Case.ROIBoundary[1][1]+Case.ROIBoundary[1][3]))
		elif Count.SwitchCount==1: #Left(2_Left) #only one ROI
			Case.Patient=list(Case.CaseLabelData.iloc[Case.CSVDataItem[0]])
			MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3]))
			MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10))		
		elif Count.SwitchCount==2: #Right(2_Right)
			Case.Patient=list(Case.CaseLabelData.iloc[Case.CSVDataItem[-1]])
			MainPage.canvas.coords(MainPage.rectangle1,(10, 10, 10, 10))
			MainPage.canvas.coords(MainPage.rectangle2,(10+Case.ROIBoundary[1][0], 10+Case.ROIBoundary[1][1], 10+Case.ROIBoundary[1][0]+Case.ROIBoundary[1][2], 10+Case.ROIBoundary[1][1]+Case.ROIBoundary[1][3]))
		Find.Change_PInfo(Find, Case.Patient)
		return 
		
	def Delete(self):                #Called by Delete_Action Function(in MainWindow Class) 
		#Check the csv DataFrame exists
		if Case.CaseLabelData.empty or len(Case.CSVDataItem)==0 or len(Case.ROIBoundary)==0 or Case.Patient == [0,0,0,0, 0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0] or Count.SwitchCount==0:
			mWarning=messagebox.showwarning(title='Warning Window',message='Please click the specific ROI data!')
			return
		
		#Ask if the user is sure to delete
		MsgBox = messagebox.askquestion ('Delete Application','Are you sure to delete this ROI ?',icon = 'warning')
		print('Delete MsgBox:', MsgBox)
		if MsgBox == 'yes':
			#ROI Square
			Count.ROICount=1 #Turn off ROI
			MainPage.canvas.coords(MainPage.rectangle1,(10, 10, 10, 10))
			MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10))
			
			#Delete the info of deleted data
			if Count.SwitchCount==1: #Left  #only one
				#CSV index
				df_index=Case.CSVDataItem[0]
				del Case.CSVDataItem[0]
				del Case.ROIBoundary[0]
				
			elif Count.SwitchCount==2: #Right 
				#CSV index
				df_index=Case.CSVDataItem[-1]
				del Case.CSVDataItem[-1]
				del Case.ROIBoundary[-1]
			
			#JPEG Image
			#Crop path
			path_crop_item=os.path.join(Database.path_Crop_Image,str(Case.CaseLabelData['Patient_ID'][df_index]))
			jpg_crop_fileName=str(Case.CaseLabelData['Image_File_Name'][df_index])+'_Crop_'+str(Case.CaseLabelData['Ultrasound_Number'][df_index])+'.jpg'
			path_crop_item=os.path.join(path_crop_item,jpg_crop_fileName)
			#Full path
			path_full_item=os.path.join(Database.path_Full_Image,str(Case.CaseLabelData['Patient_ID'][df_index]))
			jpg_full_fileName=str(Case.CaseLabelData['Image_File_Name'][df_index])+'_Full_'+str(Case.CaseLabelData['Ultrasound_Number'][df_index])+'.jpg'
			path_full_item=os.path.join(path_full_item,jpg_full_fileName)
			#delete JPG files
			if os.path.exists(path_crop_item):
				os.remove(path_crop_item)
			if os.path.exists(path_full_item):
				os.remove(path_full_item)
			
			#CSV drop out and save
			Case.CaseLabelData.drop(index=df_index,inplace=True) #inplace=True change df 
			Case.CaseLabelData.to_csv(Case.CSVPath, mode='w', header=True, index=False)
			Case.CaseLabelData = pd.read_csv(Case.CSVPath)
			Case.CaseLabelData = Case.CaseLabelData.sort_values(by=['Image_File_Name','Ultrasound_Number'],ascending=True, ignore_index=True)
			
			#Reset df_item
			Case.CSVDataItem=[]
			for i in range(0,len(Case.CaseLabelData)):
				if str(Case.CaseLabelData['Image_File_Name'][i])==str(Case.ImageName):
					Case.CSVDataItem=Case.CSVDataItem+[i]
			
			#Report Showup 
			#Case.Patient=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]
			Case.Patient=[0,0,0,0, 0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]   #Version 3
			Find.Change_PInfo(Find, Case.Patient)
			print('ROI_Boundary:', Case.ROIBoundary)
		return
	
	
class DCMControl:         #DCMControl Object: an action of Back, Next button
	def __init__(self):
		pass
	
	def Back(self):	                 #Called by Back_Action Function(in MainWindow Class) 
		if Case.ImageNumber-1<0:
			mWarning=messagebox.showwarning(title='Warning Window',message='This is the first DICOM image!')
		else:
			Case.ImageNumber=Case.ImageNumber-1
			Find.Input_image(Find, Case.ImageNumber)

	def Next(self):	                 #Called by Next_Action Function(in MainWindow Class) 
		if Case.ImageNumber+1>=len(Case.DICOM):
			mWarning=messagebox.showwarning(title='Warning Window',message='This is the final DICOM image!')
		else:
			Case.ImageNumber=Case.ImageNumber+1
			Find.Input_image(Find, Case.ImageNumber)


class Check:              #Check Object: an action of Check button
	def __init__(self):                                         #Called by __init__ Function(in MainWindow Class), set_Check_windows Function
		CheckPage.__init__(CheckPage)
		#Check List
		self.Check_Caselist=[]
	

	def Missing_messenge(self, InfoList, WrongList, Messenge):  #Called by Missing_data_check Function                   #Write missing data messenge: input a missing data list & a messenge list & the adding messenge/ return a messenge list 
		for i in range(0,len(WrongList)):
			Find = False
			index='' #var_list_messenge index
			for j in range(0,len(InfoList)):
				if WrongList[i] in InfoList[j]:
					Find = True
					index=j
					break
			if Find==False:
				InfoList=InfoList+[str(WrongList[i]+': '+Messenge)]
			elif Find==True:
				InfoList[index]=InfoList[index]+' '+Messenge
		return InfoList
	
	def Missing_data_check(self):                               #Called by Check_Action Function(in MainWindow Class)    #for not printing in CMD (using the warning messenge box) 		
		#Setting: csvFile_path_list 
		csvFile_path_list = [] #CSV path list     #Version 3 : Database.path_OriginalDB Folder only have Case CSV files 
		for FileName in os.listdir(Database.path_OriginalDB):
			if '.csv' in FileName:
				csvFile_path_list += [os.path.join(Database.path_OriginalDB, FileName)]
			
		self.Check_Caselist=[0]*len(csvFile_path_list) #Check Case List #Size: the number of Cases
		print(csvFile_path_list)
		Unlabel_DCM_Messenge=['Unlabeled DICOM File:'] #Unlabel Messenge #Version 3 (Optional)
		
		#Check Method: 
		for i in range(0,len(csvFile_path_list)): #Check data case by case
			#Setting: df (Local Variable)
			df = pd.read_csv(csvFile_path_list[i])
			df = df.sort_values(by=['Image_File_Name','Ultrasound_Number'],ascending=True, ignore_index=True)
			
			#Setting: Case_path_Crop, Case_path_Full, Case_path_DICOM (Local Variables)
			Case_path_Crop = os.path.join(Database.path_Crop_Image,os.path.basename(csvFile_path_list[i])[:-4])
			Case_path_Full = os.path.join(Database.path_Full_Image,os.path.basename(csvFile_path_list[i])[:-4])
			#Case_path_DICOM = os.path.dirname(csvFile_path_list[i])
			
			#Check List & File List: Check_DCMlist & dcmFile_list, Check_Croplist & cropFile_list, Check_Fulllist & fullFile_list
			#dcmFile_list = os.listdir(Case_path_DICOM)
			#dcmFile_list.remove(os.path.basename(csvFile_path_list[i]))
			#dcmFile_list = Find.PACS_dicom_return(Find, str(os.path.basename(csvFile_path_list[i])[:-4]), 'InstanceUID')
			dcmFile_list, _ = Find.PACS_dicom_return(Find, str(os.path.basename(csvFile_path_list[i])[:-4]))
			Check_DCMlist = [0]*len(dcmFile_list)
			if os.path.exists(Case_path_Crop):
				cropFile_list = os.listdir(Case_path_Crop) #a List of Crop JPG Names 
				Check_Croplist = [0]*len(cropFile_list) #Check Crop JPG List
			else: 
				cropFile_list, Check_Croplist = [], []
			if os.path.exists(Case_path_Full):
				fullFile_list=os.listdir(Case_path_Full) #a List of Full JPG Names
				Check_Fulllist=[0]*len(fullFile_list) #Check Full JPG List
			else: 
				fullFile_list, Check_Fulllist = [], []

			#7 types of Wrong Data + 1 Unlabed DICOM
			Unlabeled_DICOM_list=[] #Unlabeled DICOM #Doesn't have DataFrame  #Version 3(Optional)
			Missing_DICOM_list=[]   #Missing DICOM   #Has DataFrame but cannot find the DICOM
			Missing_Crop_list=[]    #Missing Crop    #Has DataFrame but cannot find the crop JPG
			Missing_Full_list=[]    #Missing Full    #Has DataFrame but cannot find the full JPG
			Missing_Label_list=[]   #Missing Label   #Has not DataFrame but can find the crop or full JPG
			Extra_Label_list=[]     #Extra Label     #Has more than one DataFrame for the crop or full JPG  V
			Extra_Crop_list=[]      #Extra Crop      #Has not DataFrame but can find the crop JPG
			Extra_Full_list=[]      #Extra Full      #Has not DataFrame but can find the full JPG

			Check_CSVlist=[]    #List: [str(df['Image_File_Name'][index])+' '+str(df['Ultrasound_Number'][index])]
			#Using CSV to check CSV, DICOM, Crop, Full items
			for df_index in range(0,len(df)):
				#Check: CSV->CSV
				if str(df['Image_File_Name'][df_index])[-10:]+' '+str(df['Ultrasound_Number'][df_index]) not in Check_CSVlist:
					Check_CSVlist+=[str(df['Image_File_Name'][df_index][-10:])+' '+str(df['Ultrasound_Number'][df_index])]
				else:
					if str(df['Image_File_Name'][df_index])[-10:]+' '+str(df['Ultrasound_Number'][df_index]) not in Extra_Label_list:
						Extra_Label_list+=[str(df['Image_File_Name'][df_index])[-10:]+' '+str(df['Ultrasound_Number'][df_index])]   #Extra_Label_list
				
				#Check: CSV->DICOM       #Necessary: Case file .csv & .dcm are in the same file dictionary (csv檔和dcm檔在同一個目錄下)
				if str(df['Image_File_Name'][df_index]) in dcmFile_list: #Sample falure case: a .dcm is missing
					Check_DCMlist[dcmFile_list.index(str(df['Image_File_Name'][df_index]))] += 1 
				else:
					if str(df['Image_File_Name'][df_index]) not in Missing_DICOM_list: 
						Missing_DICOM_list += [str(df['Image_File_Name'][df_index])]                                          #Missing_DICOM_list
				
				#Check: CSV->Crop
				cropFile_name=str(df['Image_File_Name'][df_index])+'_Crop_'+str(df['Ultrasound_Number'][df_index])+'.jpg'
				if cropFile_name in cropFile_list: #Sample Check: the Crop is in the cropFile_list
					Check_Croplist[cropFile_list.index(cropFile_name)] += 1 #Check_Croplist 
				else:  #the Crop JPG not exists
					if str(df['Image_File_Name'][df_index])[-10:]+' '+str(df['Ultrasound_Number'][df_index]) not in Missing_Crop_list: 
						Missing_Crop_list += [str(df['Image_File_Name'][df_index])[-10:]+' '+str(df['Ultrasound_Number'][df_index])]  #Missing_Crop_list 
				
				#Check: CSV->Full
				fullFile_name=str(df['Image_File_Name'][df_index])+'_Full_'+str(df['Ultrasound_Number'][df_index])+'.jpg'
				if fullFile_name in fullFile_list: #Sample Check: the full is in the fullFile_list
					Check_Fulllist[fullFile_list.index(fullFile_name)]+=1 #Check_Fulllist 
				else:  #the Full JPG not exists
					if str(df['Image_File_Name'][df_index])[-10:]+' '+str(df['Ultrasound_Number'][df_index]) not in Missing_Full_list:
						Missing_Full_list+=[str(df['Image_File_Name'][df_index])[-10:]+' '+str(df['Ultrasound_Number'][df_index])] #Missing_Full_list 
			
			""""""
			#Finding Unlabeled DICOM  #Version 3(Optional)
			for dcm_index in range(0,len(Check_DCMlist)):
				if Check_DCMlist[dcm_index]==0:
					Unlabeled_DICOM_list += [dcmFile_list[dcm_index]]
			#Unlabel_DCM_Messenge=['Unlabeled DICOM File:'] #Unlabel Messenge
			if len(Unlabeled_DICOM_list)!=0:      #Unlabel_DCM_Messenge
				Unlabel_DCM_Messenge += [str(os.path.basename(csvFile_path_list[i])[:-4])]+[Unlabeled_DICOM_list]
			""""""
			
			#Setting Check_Caselist
			if len(df)==len(cropFile_list) and len(df)==len(fullFile_list) and len(Extra_Label_list)==0 and len(Missing_DICOM_list)==0 and Check_Croplist==[1]*len(df) and Check_Fulllist==[1]*len(df):
				self.Check_Caselist[i]=1
			else: #Using Check_Croplist and Check_Fulllist to confirm Wrong Data types
				if Check_Croplist!=[1]*len(df):
					#Check_Croplist: Crop->CSV, DICOM 
					for check_index in range(0,len(Check_Croplist)): #Setting Extra_Label_list, Missing_Label_list, Extra_Crop_list, Missing_DICOM_list
						if Check_Croplist[check_index]==0: #Check CSV DataFrame not exist
							#Setting CropFileName
							CropFileName = str(cropFile_list[check_index])            #'1.2.826.0.1.3680043.2.77.83.20200211113318511.524.1_Crop_2_Left.jpg'
							DCMInstanceUID = CropFileName[0:CropFileName.index('_')]  #'1.2.826.0.1.3680043.2.77.83.20200211113318511.524.1'
							OtherInfo = CropFileName[CropFileName.index('_')+1:]      #'Crop_2_Left.jpg'
							#Setting Wrong Message
							if DCMInstanceUID[-10:]+' '+OtherInfo[5:-4] not in Missing_Label_list:
								Missing_Label_list += [DCMInstanceUID[-10:]+' '+OtherInfo[5:-4]]    #Missing_Label_list
							Extra_Crop_list += [DCMInstanceUID[-10:]+' '+OtherInfo[5:-4]]           #Extra_Crop_list: if csv is not exist then label is not finish (the JPG is extra Data)	
							if DCMInstanceUID not in dcmFile_list and DCMInstanceUID not in Missing_DICOM_list: #Complex Check: no-CSV DataFrame and DICOM yes-crop jpg
								Missing_DICOM_list += [DCMInstanceUID]
				if Check_Fulllist!=[1]*len(df):
					#Check_Fulllist: Full->CSV, DICOM
					for check_index in range(0,len(Check_Fulllist)): #Setting Extra_Label_list, Missing_Label_list, Extra_Full_list, Missing_DICOM_list
						if Check_Fulllist[check_index]==0: #Check CSV DataFrame not exist
							#Setting FullFileName
							FullFileName = str(cropFile_list[check_index])            #'1.2.826.0.1.3680043.2.77.83.20200211113318511.524.1_Crop_2_Left.jpg'
							DCMInstanceUID = FullFileName[0:FullFileName.index('_')]  #'1.2.826.0.1.3680043.2.77.83.20200211113318511.524.1'
							OtherInfo = FullFileName[FullFileName.index('_')+1:]      #'Crop_2_Left.jpg'
							#Setting Wrong Message
							if DCMInstanceUID[-10:]+' '+OtherInfo[5:-4] not in Missing_Label_list:
								Missing_Label_list += [DCMInstanceUID[-10:]+' '+OtherInfo[5:-4]]  #Missing_Label_list
							Extra_Full_list += [DCMInstanceUID[-10:]+' '+OtherInfo[5:-4]]         #Extra_Full_list: if csv is not exist then label is not finish (the JPG is extra Data)
							if DCMInstanceUID not in dcmFile_list and DCMInstanceUID not in Missing_DICOM_list: #Complex Check: no-CSV DataFrame and DICOM yes-full jpg
								Missing_DICOM_list += [DCMInstanceUID]
				
				#Setting Warning_messenge_list for the specific case (for Check_Caselist objects)
				Warning_messenge_list=[str(os.path.basename(csvFile_path_list[i])[:-4])] #Case file name 'A226043704'
				""""""
				#DICOM Unlabeled Messenge  #Version 3(Optional)
				if len(Unlabeled_DICOM_list)!=0:
					Unlabeled_DICOM_list.sort()
					Warning_messenge_list += ['Unlabeled DICOM File:']+[Unlabeled_DICOM_list]
				""""""
				#DICOM Missing Messenge
				if len(Missing_DICOM_list)!=0:
					Missing_DICOM_list.sort()
					Warning_messenge_list += ['DICOM File Missing:']+[Missing_DICOM_list]
				#A Sepicific US Wrong Messenge
				Information=[]
				Information=self.Missing_messenge(Information, Missing_Label_list, 'csvMissing') #Label
				Information=self.Missing_messenge(Information, Extra_Label_list, 'csvExtra')
				Information=self.Missing_messenge(Information, Missing_Full_list, 'FullMissing') #Full
				Information=self.Missing_messenge(Information, Extra_Full_list, 'FullExtra')
				Information=self.Missing_messenge(Information, Missing_Crop_list, 'CropMissing') #Crop
				Information=self.Missing_messenge(Information, Extra_Crop_list, 'CropExtra')
				Information.sort()
				if len(Information)!=0:
					Warning_messenge_list += ['Wrong Data Information:']+[Information]
				
				self.Check_Caselist[i]=Warning_messenge_list
			
		#Setting Check_Caselist for all correct messenge
		if self.Check_Caselist==[1]*len(csvFile_path_list):
			#self.Check_Caselist=[['--All Check!--']]
			self.Check_Caselist=[['--All Check!--']]+[Unlabel_DCM_Messenge]  #Version 3(Optional)
	

	def Scrollbar_move(self, event):                            #Called by Check_Window_Show Function                    #input a mouse event / no return 
		CheckPage.checkcanvas.configure(scrollregion=CheckPage.checkcanvas.bbox("all")) 
	
	def Show_check_data(self, Check_Caselist):                  #Called by Check_Window_Show Function                    #Show up Checking Report #input a Check list & a Canvas Frame(for Label objects on the Canvas with a Scrollbar on it)/ no return 
		lTopic=tk.Label(CheckPage.CanvasFrame,text='Checking Report',font=("Helvetica", 12, 'bold')).grid(row=0, column=0, pady=2, sticky='w')
		info_row=1 #Check_window (canvas_frame) Label objects row index
		for i in range(0,len(Check_Caselist)): #var_Check_Caselist size: len(csvFile_path_list) or 1([['--All Check!--']])
			if Check_Caselist[i]!=1:  #The case has some wrong message
				for j in range(0,len(Check_Caselist[i])):  
					if type(Check_Caselist[i][j])==str:   #str objects: var_PID, 'DICOM File Missing:', 'Wrong Data Information:'
						lStrInfo=tk.Label(CheckPage.CanvasFrame, text=Check_Caselist[i][j], font=("Helvetica", 11, 'bold')).grid(row=info_row, column=0, pady=2, sticky='w')
						info_row=info_row+1
					if type(Check_Caselist[i][j])==list:  #list objects: ['F000004 2_Left: csvExtra', 'F000004 2_Right: csvMissing CropExtra', ...]
						for info in Check_Caselist[i][j]:
							lListInfo=tk.Label(CheckPage.CanvasFrame, text='  '+info, font=("Helvetica", 10)).grid(row=info_row, column=0, sticky='w')
							info_row=info_row+1	

	def set_Check_windows(self):                                #Called by Check_Window_Show Function
		if CheckPage.CheckWindows!='':
			CheckPage.CheckWindows.destroy()
		Check.__init__(Check)
	
	
	def Check_Window_Show(self):                                #Called by Check_Action Function(in MainWindow Class)
		#Check_windows-----------------------------------------------------------------------------
		CheckPage.CheckWindows = tk.Toplevel(MainPage.Window)
		CheckPage.CheckWindows.title('Detials of Wrong Data')
		CheckPage.CheckWindows.geometry('380x400')  #version 3 
		#CheckPage.CheckWindows.geometry('350x450')
		CheckPage.CheckWindows.resizable(0,0)
		CheckPage.CheckWindows.protocol("WM_DELETE_WINDOW", self.set_Check_windows)
		
		CheckPage.FullFrame=tk.Frame(CheckPage.CheckWindows,width=380,height=400) #full_frame size: canvas + RightScrollbar
		#CheckPage.FullFrame=tk.Frame(CheckPage.CheckWindows,width=350,height=450) #full_frame size: canvas + RightScrollbar
		CheckPage.FullFrame.place(x=0,y=0)
		
		CheckPage.checkcanvas=tk.Canvas(CheckPage.FullFrame,width=360,height=400)
		#CheckPage.checkcanvas=tk.Canvas(CheckPage.FullFrame,width=330,height=450) 
		CheckPage.checkcanvas.pack(side="left") 

		CheckPage.CanvasFrame=tk.Frame(CheckPage.checkcanvas) #canvas_frame size: canvas
		CheckPage.CanvasFrame.place(x=0,y=0)
		CheckPage.checkcanvas.create_window((0,0),window=CheckPage.CanvasFrame,anchor='nw') #for tk.Label objects

		CheckPage.RightScrollbar=tk.Scrollbar(CheckPage.FullFrame,orient="vertical",command=CheckPage.checkcanvas.yview) #RightScrollbar size: width=20 height=500
		CheckPage.checkcanvas.configure(yscrollcommand=CheckPage.RightScrollbar.set) 
		CheckPage.RightScrollbar.pack(side="right",fill="y") 

		CheckPage.CanvasFrame.bind("<Configure>", self.Scrollbar_move)  #Mouse event
		self.Show_check_data(self.Check_Caselist) #Show Label objects
		

class Statistics:         #Statistics Object: an action of Statistics button  #Version 3(Keywords): PID, 'All'
	def __init__(self):                                         #Called by __init__ Function(in MainWindow Class), set_Statistics_windows Function
		StatisticsPage.__init__(StatisticsPage)
		
		self.DBCounting=['None',0,0,'None',0,0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0]        #Setting: Statistic_Count Function
		self.patientID_list=[]                                                                 #Setting: find_csvfile_path_and_patientID_list Function
		#self.finish_case_list=[]                                                              #Setting: find_csvfile_path_and_patientID_list Function
		#self.csvfile_path_list=[]                                                             #Setting: find_csvfile_path_and_patientID_list Function
		
		self.Total=['Cases Name:','Counting Cases:','Total Lesions:','Filter:']
		self.Info_side=['Left Breast:','Right Breast:']
		self.Info_tissue=['Homogeneous-fat:','Fibroglandular:','Heterogeneous:']
		self.Info_birads=['BIRADS 2:','BIRADS 3:','BIRADS 4:','BIRADS 5:']
		self.Info_size=['Under 1 cm:','Between 1-2 cm:','Between 2-3 cm:','Between 3-4 cm:']
		self.Info_depth=['Under 1 cm from skin:','1-2 cm from skin:','2-3 cm from skin:','3-4 cm from skin:']
		self.Info_ROIsize=['Smaller than 128:','Between 128 to 256:','Larger than 256:']


	def find_csvfile_path_and_patientID_list(self, DB_path):    #Called by Statistics_Action Function(in MainWindow Class)       #Find all the csvFile path and all the Patient ID(Case file name) #input DB path / no return
		self.patientID_list=[]
		#Setting patientID_list
		for FileName in os.listdir(DB_path):
			if '.csv' in FileName:
				self.patientID_list+=[FileName[:-4]]

		"""
		self.patientID_list=[]
		self.csvfile_path_list=[]
		#Find all the csv files and setting patientID_list & csvfile_path_list
		for dirpath, dirnames, filenames in os.walk(DB_path):
			for i in range(0,len(filenames)):
				if '.csv' in filenames[i]:
					self.csvfile_path_list=self.csvfile_path_list+[os.path.join(dirpath,filenames[i])]
					self.patientID_list=self.patientID_list+[os.path.basename(dirpath)]
		#self.finish_case_list=os.listdir(Database.path_Crop_Finish)
		"""
	
	def Int2Str(self, counting_number):                         #Called by Reflesh_Statistics Function                           #Counting Percentage and Changing the practical number to a string of value info #input a integer number / return a string 
		if self.DBCounting[2]==0:  #c_total_image
			return str(0)+'('+str(0)+'%)'
		else:
			return str(counting_number)+'('+str(round(counting_number*100/self.DBCounting[2],2))+'%)'

	def Reflesh_Statistics(self):                               #Called by Statistic_Count Function                              #Reset tkinter (Label Objects)		
		StatisticsPage.lCaseName.config(text=self.DBCounting[0])       #var_patientID
		StatisticsPage.lCountingCase.config(text=self.DBCounting[1])   #c_total_case
		StatisticsPage.lTatalImage.config(text=self.DBCounting[2])     #c_total_image
		StatisticsPage.lBIRADSFilter.config(text=self.DBCounting[3])   #var_filter
		
		StatisticsPage.lLeft.config(text=self.Int2Str(self.DBCounting[4]))  #c_side_left
		StatisticsPage.lRight.config(text=self.Int2Str(self.DBCounting[5])) #c_side_right
		
		StatisticsPage.lFat.config(text=self.Int2Str(self.DBCounting[6]))   #c_tissue_fat
		StatisticsPage.lFibro.config(text=self.Int2Str(self.DBCounting[7])) #c_tissue_fibroglandular
		StatisticsPage.lHetero.config(text=self.Int2Str(self.DBCounting[8]))#c_tissue_heterogeneous 
		
		StatisticsPage.lBIRADS2.config(text=self.Int2Str(self.DBCounting[9]))  #c_birads_2
		StatisticsPage.lBIRADS3.config(text=self.Int2Str(self.DBCounting[10])) #c_birads_3
		StatisticsPage.lBIRADS4.config(text=self.Int2Str(self.DBCounting[11])) #c_birads_4
		StatisticsPage.lBIRADS5.config(text=self.Int2Str(self.DBCounting[12])) #c_birads_5
		
		StatisticsPage.lSize1.config(text=self.Int2Str(self.DBCounting[13]))   #c_mass_size_1
		StatisticsPage.lSize2.config(text=self.Int2Str(self.DBCounting[14]))   #c_mass_size_2
		StatisticsPage.lSize3.config(text=self.Int2Str(self.DBCounting[15]))   #c_mass_size_3
		StatisticsPage.lSize4.config(text=self.Int2Str(self.DBCounting[16]))   #c_mass_size_4

		StatisticsPage.lDepth1.config(text=self.Int2Str(self.DBCounting[17]))  #c_mass_depth_1
		StatisticsPage.lDepth2.config(text=self.Int2Str(self.DBCounting[18]))  #c_mass_depth_2
		StatisticsPage.lDepth3.config(text=self.Int2Str(self.DBCounting[19]))  #c_mass_depth_3
		StatisticsPage.lDepth4.config(text=self.Int2Str(self.DBCounting[20]))  #c_mass_depth_4 
		
		StatisticsPage.lROIs128.config(text=self.Int2Str(self.DBCounting[21])) #c_ROI_s128
		StatisticsPage.lROIs256.config(text=self.Int2Str(self.DBCounting[22])) #c_ROI_s256
		StatisticsPage.lROImore.config(text=self.Int2Str(self.DBCounting[23])) #c_ROI_more

	def statistics_per_case(self, var_csvfile_path, var_BIRADS_Filter):   #Called by Statistic_Count Function                    #Statistics a single case (Setting DBCounting) #input the specific csvfile path and the BIRADS filter info(string) / no return  
		#Open CSV and set the original df
		df = pd.read_csv(var_csvfile_path)
		df = df.sort_values(by=['Image_File_Name','Ultrasound_Number'],ascending=True,ignore_index=True)
		#Note: df_after=df => if df_after change -> df change (df_after not copy df, only give a point to df)
		
		#Setting the counting df (Optional)
		CSV_BIRADS_original=list(df['BIRADS_Level'])   #Note: df['BIRADS_Level'][i] => take out the i-index value (CSV index is not always equal to the number of sequence)
		if str(var_BIRADS_Filter)!='None':
			for i in range(0,len(CSV_BIRADS_original)):
				for index in range(2,6):
					if str(index) in str(CSV_BIRADS_original[i]) and str(index) not in str(var_BIRADS_Filter):
						df.drop(index=i,inplace=True)
		
		#Counting
		self.DBCounting[1] = self.DBCounting[1]+1       #c_total_case
		self.DBCounting[2] = self.DBCounting[2]+len(df)	#c_total_image
		for i in range(0,len(df)):
			#Breast Side
			if str(list(df['Breast_Side'])[i])=='Left':
				self.DBCounting[4] = self.DBCounting[4]+1    #c_side_left
			elif str(list(df['Breast_Side'])[i])=='Right':
				self.DBCounting[5] = self.DBCounting[5]+1    #c_side_right
			#Breast Tissue
			if str(list(df['Tissue_Composition'])[i])=='Homogeneous-Fat':
				self.DBCounting[6] = self.DBCounting[6]+1    #c_tissue_fat
			elif str(list(df['Tissue_Composition'])[i])=='Fibroglandular':
				self.DBCounting[7] = self.DBCounting[7]+1    #c_tissue_fibroglandular
			elif str(list(df['Tissue_Composition'])[i])=='Heterogeneous':
				self.DBCounting[8] = self.DBCounting[8]+1    #c_tissue_heterogeneous
			#BI-RADS Category
			if str(list(df['BIRADS_Level'])[i])=='Category 2':
				self.DBCounting[9] = self.DBCounting[9]+1    #c_birads_2
			elif str(list(df['BIRADS_Level'])[i])=='Category 3':
				self.DBCounting[10] = self.DBCounting[10]+1  #c_birads_3
			elif str(list(df['BIRADS_Level'])[i])=='Category 4':
				self.DBCounting[11] = self.DBCounting[11]+1	 #c_birads_4
			elif str(list(df['BIRADS_Level'])[i])=='Category 5':
				self.DBCounting[12] = self.DBCounting[12]+1	 #c_birads_5
			#Mass Lesion Size
			if float(list(df['Mass_Size'])[i][:-3])<=float(1) and float(list(df['Mass_Size'])[i][:-3])>float(0):
				self.DBCounting[13] = self.DBCounting[13]+1  #c_mass_size_1
			elif float(list(df['Mass_Size'])[i][:-3])<=float(2) and float(list(df['Mass_Size'])[i][:-3])>float(1):
				self.DBCounting[14] = self.DBCounting[14]+1	 #c_mass_size_2	 
			elif float(list(df['Mass_Size'])[i][:-3])<=float(3) and float(list(df['Mass_Size'])[i][:-3])>float(2):
				self.DBCounting[15] = self.DBCounting[15]+1	 #c_mass_size_3
			elif float(list(df['Mass_Size'])[i][:-3])<=float(4) and float(list(df['Mass_Size'])[i][:-3])>float(3):
				self.DBCounting[16] = self.DBCounting[16]+1  #c_mass_size_4
			#Mass Lesion Depth	
			if float(list(df['Lesion_Depth'])[i][:-3])<=float(1) and float(list(df['Lesion_Depth'])[i][:-3])>float(0):
				self.DBCounting[17] = self.DBCounting[17]+1  #c_mass_depth_1
			elif float(list(df['Lesion_Depth'])[i][:-3])<=float(2) and float(list(df['Lesion_Depth'])[i][:-3])>float(1):
				self.DBCounting[18] = self.DBCounting[18]+1  #c_mass_depth_2
			elif float(list(df['Lesion_Depth'])[i][:-3])<=float(3) and float(list(df['Lesion_Depth'])[i][:-3])>float(2):
				self.DBCounting[19] = self.DBCounting[19]+1	 #c_mass_depth_3
			elif float(list(df['Lesion_Depth'])[i][:-3])<=float(4) and float(list(df['Lesion_Depth'])[i][:-3])>float(3):
				self.DBCounting[20] = self.DBCounting[20]+1	 #c_mass_depth_4
			#ROI Size
			H_index=list(df['ROI_Image_Size'])[i].index('H')
			SquareSize=int(list(df['ROI_Image_Size'])[i][H_index+2:])
			if SquareSize<=128:
				self.DBCounting[21] = self.DBCounting[21]+1  #c_ROI_s128
			elif SquareSize<=256 and SquareSize>128:
				self.DBCounting[22] = self.DBCounting[22]+1  #c_ROI_s256
			elif SquareSize>256:
				self.DBCounting[23] = self.DBCounting[23]+1  #c_ROI_more

	def Statistic_Count(self):                                            #Called by Statistics_Window_Show Function                               #The main logic of counting csv data #no input / no return
		self.DBCounting=['None',0,0,'None',0,0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0]           #initialize global variables
		self.Reflesh_Statistics()     #reset tkinter Label objects

		#Setting DBCounting[3](var_filter)
		if StatisticsPage.eBIRADS.get()!='':
			self.DBCounting[3]=str(StatisticsPage.eBIRADS.get())
		else:
			self.DBCounting[3]='None'
		
		#Setting different model of counting and keywords           #Version 3: Cancel Finished Cases Counting
		if StatisticsPage.ePatientName.get()=='All':                #All Cases Counting
			self.DBCounting[0] = 'All'
			for i in range(0,len(self.patientID_list)):
				self.statistics_per_case(os.path.join(Database.path_OriginalDB, str(self.patientID_list[i])+'.csv'), self.DBCounting[3])
		elif StatisticsPage.ePatientName.get() in self.patientID_list:   #the specific Case Counting
			self.DBCounting[0] = StatisticsPage.ePatientName.get()
			index=self.patientID_list.index(str(self.DBCounting[0]))
			self.statistics_per_case(os.path.join(Database.path_OriginalDB, str(self.patientID_list[index])+'.csv'), self.DBCounting[3])
		elif StatisticsPage.ePatientName.get()=='':                 #None Input / Initialize
			self.DBCounting=['None',0,0,'None',0,0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0]
		else:                                        #Not correct keyworads input warning
			mWarning=messagebox.showwarning(title='Warning Window',message='The Keyword is WRONG!', parent=StatisticsPage.StatisticsWindows)
			return
			
		self.Reflesh_Statistics()   #set tkinter Label objects
   	
	def set_Statistics_windows(self):                                     #Called by Statistics_Window_Show Function
		if StatisticsPage.StatisticsWindows!='':
			StatisticsPage.StatisticsWindows.destroy()
		Statistics.__init__(Statistics)


	def Statistics_Window_Show(self):		                              #Called by Statistics_Action Function(in MainWindow Class)
		#Statistics_windows-----------------------------------------------
		StatisticsPage.StatisticsWindows = tk.Toplevel(MainPage.Window)
		StatisticsPage.StatisticsWindows.title('Statistics Window')
		StatisticsPage.StatisticsWindows.geometry('590x570')#uint:('widthxhight')
		StatisticsPage.StatisticsWindows.resizable(0,0)
		StatisticsPage.StatisticsWindows.protocol("WM_DELETE_WINDOW", self.set_Statistics_windows)
		
		#font decision
		f_title1 = font.Font(family="Helvetica", size=12, weight='bold')
		f_title2 = font.Font(family="Helvetica", size=10, weight='bold',underline=1)
		f_title3 = font.Font(family="Helvetica", size=9, weight='bold')
		f_content1 = font.Font(family="Helvetica", size=12)
		f_content2 = font.Font(family="Helvetica", size=10)
		f_content3 = font.Font(family="Helvetica", size=9)
		
		#mode frame
		StatisticsPage.ModeFrame=tk.Frame(StatisticsPage.StatisticsWindows)
		StatisticsPage.ePatientName = tk.Entry(StatisticsPage.ModeFrame,font=f_content1, show=None)
		StatisticsPage.ePatientName.grid(row=0, column=0, columnspan=2, padx=5, pady=1,sticky='w')
		StatisticsPage.bCount = tk.Button(StatisticsPage.ModeFrame, text='Count',font=f_content2, command=self.Statistic_Count) #
		StatisticsPage.bCount.grid(row=0, column=3, columnspan=1, padx=5, pady=1,sticky='w')
		StatisticsPage.lEmpty = tk.Label(StatisticsPage.ModeFrame, text=' ', font=f_content2, anchor='w')
		StatisticsPage.lEmpty.grid(row=0, column=5, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lFilter = tk.Label(StatisticsPage.ModeFrame, text='Filter:',font=f_content1)
		StatisticsPage.lFilter.grid(row=0, column=7, columnspan=1, padx=5, pady=1,sticky='w')
		StatisticsPage.eBIRADS = tk.Entry(StatisticsPage.ModeFrame,font=f_content1,width=15, show=None)#BIRADS 5 / 5
		StatisticsPage.eBIRADS.grid(row=0, column=9, padx=5, pady=1,sticky='w')
		StatisticsPage.ModeFrame.pack(side='top', anchor='nw', fill='x', expand='no')

		#statistic frame
		StatisticsPage.StatisticFrame=tk.Frame(StatisticsPage.StatisticsWindows)
		StatisticsPage.lStatisticsReport = tk.Label(StatisticsPage.StatisticFrame, text='Statistics Report: ', font=f_title1, anchor='center')
		StatisticsPage.lStatisticsReport.grid(row=0, column=0, columnspan=3, pady=1,sticky='w')


		rowGlobal=1
		columnGlobal=0
		for VariableName in self.Total:
			r1 = tk.Label(StatisticsPage.StatisticFrame, text=VariableName, font=f_title3, anchor='w')
			r1.grid(row=rowGlobal, column=columnGlobal, columnspan=1, padx=5,sticky='w')
			columnGlobal=columnGlobal+2	
		StatisticsPage.lCaseName = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[0], font=f_content2, anchor='w')
		StatisticsPage.lCaseName.grid(row=rowGlobal+1, column=0, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lCountingCase = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[1], font=f_content2, anchor='w')
		StatisticsPage.lCountingCase.grid(row=rowGlobal+1, column=2, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lTatalImage = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[2], font=f_content2, anchor='w')
		StatisticsPage.lTatalImage.grid(row=rowGlobal+1, column=4, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lBIRADSFilter = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[3], font=f_content2, anchor='w')
		StatisticsPage.lBIRADSFilter.grid(row=rowGlobal+1, column=6, columnspan=1, padx=5,sticky='w')


		StatisticsPage.lOverAll = tk.Label(StatisticsPage.StatisticFrame, text='Over All US Information', font=f_title1, anchor='center').grid(row=3, column=0, columnspan=1,sticky='w')

		rowSide=5
		columnSide=0
		StatisticsPage.lBreastSide = tk.Label(StatisticsPage.StatisticFrame, text='Breast Side', font=f_title2, anchor='center').grid(row=4, column=0, columnspan=1,sticky='w')
		for VariableName in self.Info_side:
			r1 = tk.Label(StatisticsPage.StatisticFrame, text=VariableName, font=f_title3, anchor='w')
			r1.grid(row=rowSide, column=columnSide, columnspan=1, padx=5,sticky='w')
			columnSide=columnSide+2
		StatisticsPage.lLeft = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[4], font=f_content2, anchor='w')
		StatisticsPage.lLeft.grid(row=rowSide+1, column=0, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lRight = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[5], font=f_content2, anchor='w')
		StatisticsPage.lRight.grid(row=rowSide+1, column=2, columnspan=1, padx=5,sticky='w')	
			

		rowTissue=8
		columnTissue=0
		StatisticsPage.lBreastTissue = tk.Label(StatisticsPage.StatisticFrame, text='Tissue Composition', font=f_title2, anchor='center').grid(row=7, column=0, columnspan=1,sticky='w')
		for VariableName in self.Info_tissue:
			r1 = tk.Label(StatisticsPage.StatisticFrame, text=VariableName, font=f_title3, anchor='w')
			r1.grid(row=rowTissue, column=columnTissue, columnspan=1, padx=5,sticky='w')
			columnTissue=columnTissue+2
		StatisticsPage.lFat = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[6], font=f_content2, anchor='w')
		StatisticsPage.lFat.grid(row=rowTissue+1, column=0, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lFibro = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[7], font=f_content2, anchor='w')
		StatisticsPage.lFibro.grid(row=rowTissue+1, column=2, columnspan=1, padx=5,sticky='w')	
		StatisticsPage.lHetero = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[8], font=f_content2, anchor='w')
		StatisticsPage.lHetero.grid(row=rowTissue+1, column=4, columnspan=1, padx=5,sticky='w')	

		StatisticsPage.lFullImage = tk.Label(StatisticsPage.StatisticFrame, text='Mass Lesion Feature', font=f_title1, anchor='center').grid(row=10, column=0, columnspan=1,sticky='w')

		rowBIRADS=12
		columnBIRADS=0
		StatisticsPage.lBreastBIRADS = tk.Label(StatisticsPage.StatisticFrame, text='BI-RADS Level', font=f_title2, anchor='center').grid(row=11, column=0, columnspan=1,sticky='w')
		for VariableName in self.Info_birads:
			r1 = tk.Label(StatisticsPage.StatisticFrame, text=VariableName, font=f_title3, anchor='w')
			r1.grid(row=rowBIRADS, column=columnBIRADS, columnspan=1, padx=5,sticky='w')
			columnBIRADS=columnBIRADS+2
		StatisticsPage.lBIRADS2 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[9], font=f_content2, anchor='w')
		StatisticsPage.lBIRADS2.grid(row=rowBIRADS+1, column=0, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lBIRADS3 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[10], font=f_content2, anchor='w')
		StatisticsPage.lBIRADS3.grid(row=rowBIRADS+1, column=2, columnspan=1, padx=5,sticky='w')	
		StatisticsPage.lBIRADS4 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[11], font=f_content2, anchor='w')
		StatisticsPage.lBIRADS4.grid(row=rowBIRADS+1, column=4, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lBIRADS5 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[12], font=f_content2, anchor='w')
		StatisticsPage.lBIRADS5.grid(row=rowBIRADS+1, column=6, columnspan=1, padx=5,sticky='w')	


		rowSize=15
		columnSize=0
		StatisticsPage.lSize = tk.Label(StatisticsPage.StatisticFrame, text='Mass Size', font=f_title2, anchor='center').grid(row=14, column=0, columnspan=1,sticky='w')
		for VariableName in self.Info_size:
			r1 = tk.Label(StatisticsPage.StatisticFrame, text=VariableName, font=f_title3, anchor='w')
			r1.grid(row=rowSize, column=columnSize, columnspan=1, padx=5,sticky='w')
			columnSize=columnSize+2
		StatisticsPage.lSize1 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[13], font=f_content2, anchor='w')
		StatisticsPage.lSize1.grid(row=rowSize+1, column=0, columnspan=1, padx=5,sticky='w')	
		StatisticsPage.lSize2 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[14], font=f_content2, anchor='w')
		StatisticsPage.lSize2.grid(row=rowSize+1, column=2, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lSize3 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[15], font=f_content2, anchor='w')
		StatisticsPage.lSize3.grid(row=rowSize+1, column=4, columnspan=1, padx=5,sticky='w')		
		StatisticsPage.lSize4 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[16], font=f_content2, anchor='w')
		StatisticsPage.lSize4.grid(row=rowSize+1, column=6, columnspan=1, padx=5,sticky='w')

			
		rowDepth=18
		columnDepth=0
		StatisticsPage.lDepth = tk.Label(StatisticsPage.StatisticFrame, text='Mass Depth', font=f_title2, anchor='center').grid(row=17, column=0, columnspan=1,sticky='w')
		for VariableName in self.Info_depth:
			r1 = tk.Label(StatisticsPage.StatisticFrame, text=VariableName, font=f_title3, anchor='w')
			r1.grid(row=rowDepth, column=columnDepth, columnspan=1, padx=5,sticky='w')
			columnDepth=columnDepth+2
		StatisticsPage.lDepth1 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[17], font=f_content2, anchor='w')
		StatisticsPage.lDepth1.grid(row=rowDepth+1, column=0, columnspan=1, padx=5,sticky='w')	
		StatisticsPage.lDepth2 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[18], font=f_content2, anchor='w')
		StatisticsPage.lDepth2.grid(row=rowDepth+1, column=2, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lDepth3 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[19], font=f_content2, anchor='w')
		StatisticsPage.lDepth3.grid(row=rowDepth+1, column=4, columnspan=1, padx=5,sticky='w')		
		StatisticsPage.lDepth4 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[20], font=f_content2, anchor='w')
		StatisticsPage.lDepth4.grid(row=rowDepth+1, column=6, columnspan=1, padx=5,sticky='w')


		rowROI=21
		columnROI=0
		StatisticsPage.lROI = tk.Label(StatisticsPage.StatisticFrame, text='ROI Size', font=f_title2, anchor='center').grid(row=20, column=0, columnspan=1,sticky='w')
		for VariableName in self.Info_ROIsize:
			r1 = tk.Label(StatisticsPage.StatisticFrame, text=VariableName, font=f_title3, anchor='w')
			r1.grid(row=rowROI, column=columnROI, columnspan=1, padx=5,sticky='w')
			columnROI=columnROI+2
		StatisticsPage.lROIs128 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[21], font=f_content2, anchor='w')
		StatisticsPage.lROIs128.grid(row=rowROI+1, column=0, columnspan=1, padx=5,sticky='w')	
		StatisticsPage.lROIs256 = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[22], font=f_content2, anchor='w')
		StatisticsPage.lROIs256.grid(row=rowROI+1, column=2, columnspan=1, padx=5,sticky='w')
		StatisticsPage.lROImore = tk.Label(StatisticsPage.StatisticFrame, text=self.DBCounting[23], font=f_content2, anchor='w')
		StatisticsPage.lROImore.grid(row=rowROI+1, column=4, columnspan=1, padx=5,sticky='w')		

		StatisticsPage.StatisticFrame.pack(side='top', anchor='nw', fill='both', expand='no')


class Deidentify:         #Deidentify Object: an action of Deidentify button
	def __init__(self):                                                                      #Called by __init__ Function(in MainWindow Class)
		#Version 3: (total 25->20) Delete Vitual_FileName, Real_FileName, DICOM_FileName, DICOM_Instance_Number, Vitaul_MediaSOPInstanceUID, Real_MediaSOPInstanceUID / Add Vitual_DICOMName	
		self.title=['Virtual_PatientName', 'Real_PatientName', 'Removed_PatientID', 'Removed_PatientBirthDate', 'Virtual_DICOMName',  
			'Virtual_StudyDate', 'Real_StudyDate', 'Virtual_ContentDate', 'Real_ContentDate', 'Removed_StudyTime', 'Removed_ContentTime',
			'Virtual_StudyInstanceUID', 'Real_StudyInstanceUID', 'Virtual_SeriesInstanceUID', 'Real_SeriesInstanceUID',
			'Virtual_SOPInstanceUID', 'Real_SOPInstanceUID', 'Virtual_RefSOPInstanceUID', 'Real_RefSOPInstanceUID',
			'PixelData']
		
		#(4)Patient Infomation: 'Virtual_PatientName', 'Real_PatientName', 'Removed_PatientID', 'Removed_PatientBirthDate'  
		#(1)DICOM Name: 'Virtual_DICOMName'  
		#(6)DICOM Study Date & Time: 'Virtual_StudyDate', 'Real_StudyDate', 'Virtual_ContentDate', 'Real_ContentDate', 'Removed_StudyTime', 'Removed_ContentTime'
		#(4)DICOM Study/Series/Instance/Reference UID: 'Virtual_StudyInstanceUID', 'Real_StudyInstanceUID', 'Virtual_SeriesInstanceUID', 'Real_SeriesInstanceUID'
		#(4)DICOM Study/Series/Instance/Reference UID:	'Virtual_SOPInstanceUID', 'Real_SOPInstanceUID', 'Virtual_RefSOPInstanceUID', 'Real_RefSOPInstanceUID'
		#(1)DICOM Pixel Data: 'PixelData'
		
		#Version 3: (total 22->20) Delete Patient_File_Name, Full_Image_Path / Sort Patient_Flow_Number to the FIRST Column
		#Deidentification CSV Title
		self.groups = ["Patient_Flow_Number", "Image_File_Name", "DICOM_Instance", 
			"Ultrasound_Number", "Breast_Side", "Tissue_Composition", "BIRADS_Level", "Mass_Shape", "Mass_Margin",
			"Mass_Orientation", "Echo_Pattern", "Posterior_Feature", "Calcification", "Mass_Size", "Lesion_Depth", "Lesion_Location", 
			"Full_Size", "ROI_Start_Location", "ROI_Image_Size"] 
		
		#Patient Info: 3 (DICOM: 2)
		#US Description: 3
		#Lesion Feature: 10
		#ROI Description: 4
		
		self.DeDICOMDB_path=os.path.join(Database.path_Deidentify,'1. DICOM File')
		self.DeCSVDB_path=os.path.join(Database.path_Deidentify,'2. CSV File')
		self.DeCropDB_path=os.path.join(Database.path_Deidentify,'3. Cropped US Image')
		self.DeFullDB_path=os.path.join(Database.path_Deidentify,'4. Full US Image')
		
	"""	
	#Version 2
	def Change_PatientName(self, var_CSV_df, var_DICOMTag_value):    #Called by DCMTag_Deidentification Function    #Input DeCSV df & Real Patient Name / return Virtual Patient Name (Use Real Patient Name to find Virtual Patient Name)
		#PatientID_list=list(var_CSV_df['Removed_PatientID'])       #Real Patient ID
		Real_FileName_list=list(var_CSV_df['Real_FileName'])       #Real Patient Name
		Virtual_FileName_list=list(var_CSV_df['Virtual_FileName']) #Virtual Patient Name
		#Setting new DICOMTag value(Patient Name)
		if var_DICOMTag_value in Real_FileName_list:  #if Real Patient Name exists in csv, take out the Virtual Patient Name
			index=Real_FileName_list.index(var_DICOMTag_value)
			new_DICOMTag_value=Virtual_FileName_list[index]	
		else:                                         #if Real Patient Name not exist in csv, take out the least Virtual Patient Name and get the new Virtual Patient Name
			if len(Virtual_FileName_list)==0:
				new_DICOMTag_value='P_0001'
			else:
				new_vale=str(int(Virtual_FileName_list[-1][2:])+1)
				new_DICOMTag_value='P_'+'0'*(4-len(new_vale))+new_vale
		return new_DICOMTag_value
	"""
	
	
	def Change_StudyInstanceUID(self, var_DeCSV_df, var_DICOMTag_value, var_CaseFile_name):  #Called by DCMTag_Deidentification Function   #Input DeCSV df & Real Study Instance UID(0020, 000D) & Case File Name 'P_0001'/ return Virtual Study Instance UID  #Usage: DICOM Tag (0020,000D), (0020,000E)
		StudyUID_list=list(var_DeCSV_df['Real_StudyInstanceUID'])
		Virtual_StudyUID_list=list(var_DeCSV_df['Virtual_StudyInstanceUID'])
		#Setting new DICOMTag value(Study Instance UID) [1/per Study(Patient Case)]
		if var_DICOMTag_value in StudyUID_list:
			index=StudyUID_list.index(var_DICOMTag_value)
			new_DICOMTag_value=Virtual_StudyUID_list[index]	
		else:
			#String -> List
			UID_List=var_DICOMTag_value.split('.')
			#Coding
			Coding_item=list(UID_List[-2])   #Coding item: String -> List 
			random.shuffle(Coding_item)      #Coding item: shuffle List 
			UID_List[-2]=''.join(Coding_item)
			new_DICOMTag_value = '1.2.112.0.1.' + UID_List[-2] + '.' + var_CaseFile_name[2:]
		return new_DICOMTag_value

	def Change_SOPInstanceUID(self, var_DeCSV_df, var_DICOMTag_value, var_DICOMFile_name):   #Called by DCMTag_Deidentification Function   #Input DeCSV df & Real Media SOP Instance UID(0002, 0003) & DICOM File Name 'F000001'/ return SOP Instance UID  #Usage: DICOM Tag (0002,0003), (0008,0018)
		SOPUID_list=list(var_DeCSV_df['Real_SOPInstanceUID'])
		Virtual_SOPUID_list=list(var_DeCSV_df['Virtual_SOPInstanceUID'])
		#Setting new DICOMTag value(Media SOP Instance UID) [1/per Instance(DICOM file)]
		if var_DICOMTag_value in SOPUID_list:
			index=SOPUID_list.index(var_DICOMTag_value)
			new_DICOMTag_value=Virtual_SOPUID_list[index]	
		else:
			#String -> List
			UID_List=var_DICOMTag_value.split('.')
			#Coding
			Coding_item=list(UID_List[-3])   #Coding item: String -> List 
			random.shuffle(Coding_item)      #Coding item: shuffle List 
			UID_List[-3]=''.join(Coding_item)
			new_DICOMTag_value='1.2.514.0.1.'+UID_List[-3]+'.'+var_DICOMFile_name[1:]+'.1'
		return new_DICOMTag_value
	
	def Change_RefSOPInstanceUID(self, var_DeCSV_df, var_DICOMTag_value):                    #Called by DCMTag_Deidentification Function   #Input DeCSV df & Real Referenced SOP Instance UID(0008, 1155) / return Virtual Referenced SOP Instance UID  #Usage: DICOM Tag (0008,1155)
		RefSOPUID_list=list(var_DeCSV_df['Real_RefSOPInstanceUID'])
		Virtual_RefSOPUID_list=list(var_DeCSV_df['Virtual_RefSOPInstanceUID'])
		#Setting new DICOMTag value(Referenced SOP Instance UID) [1/per Instance(DICOM file)]
		if var_DICOMTag_value in RefSOPUID_list:
			index=RefSOPUID_list.index(var_DICOMTag_value)
			new_DICOMTag_value=Virtual_RefSOPUID_list[index]	
		else:
			#String -> List
			UID_List=var_DICOMTag_value.split('.')
			#Coding
			Coding_item=list(UID_List[-3])   #Coding item: String -> List 
			random.shuffle(Coding_item)      #Coding item: shuffle List 
			UID_List[-3]=''.join(Coding_item)
			new_DICOMTag_value='1.2.303.0.1.'+UID_List[-3]+'.1'
		return new_DICOMTag_value

	def Change_PixelData(self, var_pixel_array):            #Version 3 : faster algorithm    #Called by DCMTag_Deidentification Function   #Input Real Pixel Data(7EF0,0010) (np.array) / return Virtual Pixel Data (np.array)
		var_pixel_array[0:35, 100:880, :]=var_pixel_array[0,0,:]
		return var_pixel_array.astype(np.uint8)
	
	#Data: DICOM File   #Version 3 : Deidentify DICOM image case by case and record in DeCSV file more clearly
	def DCMTag_Deidentification(self, var_DCM_ds, var_VirtualCaseName, var_VirtualDCMName, var_DeCSV_df):          #Called by Deidentification Function       #Input a DCM Data, VirtualCaseName, VirtualDCMName / return DeCSVData
		DeCSVData=[0]*20
		#-----------------Patient Infomation-----------------
		#DeCSVData[0] : Vitual_PatientName         
		DeCSVData[0] = var_VirtualCaseName         #'P_0001'
		
		#DeCSVData[1] : Real_PatientName           #(0010, 0010) Patient's Name
		DeCSVData[1] = var_DCM_ds.PatientName     #var_DCM_ds: ds
		var_DCM_ds.PatientName = var_VirtualCaseName
		
		#DeCSVData[2] : Removed_PatientID          #(0010, 0020) PatientID
		DeCSVData[2] = var_DCM_ds.PatientID       #'A123456789'
		var_DCM_ds.PatientID = ''
		#var_DCM_ds.PatientID = var_VirtualCaseName
		
		#DeCSVData[3] : Removed_PatientBirthDate   #(0010, 0030) PatientBirthDate
		DeCSVData[3] = var_DCM_ds.PatientBirthDate            #'19990115'
		var_DCM_ds.PatientBirthDate = ''
		
		#DeCSVData[4] : Virtual_DICOMName
		DeCSVData[4] = var_VirtualDCMName          #'F000001'
		
		#-----------------Screening Infomation-----------------
		#DeCSVData[5] : Virtual_StudyDate
		DeCSVData[5] = var_DCM_ds.StudyDate[0:-2]+'01'
		
		#DeCSVData[6] : Real_StudyDate             #(0008, 0020) StudyDate
		DeCSVData[6] = var_DCM_ds.StudyDate        #'20190625'
		var_DCM_ds.StudyDate = var_DCM_ds.StudyDate[0:-2]+'01'
		
		#DeCSVData[7] : Virtual_ContentDate
		DeCSVData[7] = var_DCM_ds.ContentDate[0:-2]+'01'
			
		#DeCSVData[8] : Real_ContentDate           #(0008, 0023) ContentDate
		DeCSVData[8] = var_DCM_ds.ContentDate      #'20190625'
		var_DCM_ds.ContentDate=var_DCM_ds.ContentDate[0:-2]+'01'
		
		#DeCSVData[9] : Removed_StudyTime          #(0008, 0030) StudyTime
		DeCSVData[9] = var_DCM_ds.StudyTime        #'195512.000000'
		var_DCM_ds.StudyTime = ''
		
		#DeCSVData[10] : Removed_ContentTime       #(0008, 0033) ContentTime
		DeCSVData[10] = var_DCM_ds.ContentTime     #'195628.000000'
		var_DCM_ds.ContentTime = ''
		
		#-----------------Instance UID Infomation-----------------
		#DeCSVData[12] : Real_StudyInstanceUID             #(0020, 000D) StudyInstanceUID
		DeCSVData[12] = str(var_DCM_ds.StudyInstanceUID)   
		
		#DeCSVData[11] : Virtual_StudyInstanceUID          #ds.StudyInstanceUID='1.2.112.0.1.789456'
		var_DCM_ds.StudyInstanceUID = self.Change_StudyInstanceUID(self, var_DeCSV_df, str(var_DCM_ds.StudyInstanceUID), var_VirtualCaseName)
		DeCSVData[11] = str(var_DCM_ds.StudyInstanceUID)
		
		
		#DeCSVData[14] : Real_SeriesInstanceUID            #(0020, 000E) SeriesInstanceUID
		DeCSVData[14] = str(var_DCM_ds.SeriesInstanceUID)  

		#DeCSVData[13] : Virtual_SeriesInstanceUID         #ds.SeriesInstanceUID='1.2.112.0.1.789456.1'
		var_DCM_ds.SeriesInstanceUID  = var_DCM_ds.StudyInstanceUID + '.' + str(var_DCM_ds.SeriesNumber)
		DeCSVData[13] = str(var_DCM_ds.SeriesInstanceUID)
			
			
		#DeCSVData[16] : Real_SOPInstanceUID               #(0008, 0018) SOPInstanceUID  &  (0002, 0003) MediaStorageSOPInstanceUID
		DeCSVData[16] = str(var_DCM_ds.SOPInstanceUID)
		
		#DeCSVData[15] : Virtual_SOPInstanceUID            #ds.SOPInstanceUID='1.2.514.0.1.456789.1'
		var_DCM_ds.SOPInstanceUID = self.Change_SOPInstanceUID(self, var_DeCSV_df, str(var_DCM_ds.SOPInstanceUID), var_VirtualDCMName)
		var_DCM_ds.file_meta.MediaStorageSOPInstanceUID = var_DCM_ds.SOPInstanceUID
		DeCSVData[15] = str(var_DCM_ds.SOPInstanceUID)
		
		
		#DeCSVData[18] : Real_RefSOPInstanceUID           #(0008, 1155) ReferencedSOPInstanceUID
		DeCSVData[18] = var_DCM_ds.SourceImageSequence[0].ReferencedSOPInstanceUID
		
		#DeCSVData[17] : Virtual_RefSOPInstanceUID        #ds.SourceImageSequence[0].ReferencedSOPInstanceUID='1.3.303.789456.1'
		var_DCM_ds.SourceImageSequence[0].ReferencedSOPInstanceUID=self.Change_RefSOPInstanceUID(self, var_DeCSV_df, str(var_DCM_ds.SourceImageSequence[0].ReferencedSOPInstanceUID))
		DeCSVData[17] = str(var_DCM_ds.SourceImageSequence[0].ReferencedSOPInstanceUID)
		
		
		#-----------------Pixel Data Infomation-----------------
		#DeCSVData[19] : PixelData                 #(7FE0, 0010) PixelData
		DeCSVData[19] = var_DCM_ds.pixel_array[0:35, 100:880, :]
		DicomPixel = self.Change_PixelData(self, var_DCM_ds.pixel_array).tobytes()
		var_DCM_ds.decompress()
		var_DCM_ds.PixelData=DicomPixel  
		var_DCM_ds.PhotometricInterpretation='RGB'
		
		
		#Save
		#Save Deidentification DICOM file
		DeDICOMPath = os.path.join(os.path.join(self.DeDICOMDB_path, var_VirtualCaseName), var_VirtualDCMName)  #the Case DeDCM folder has been created.
		var_DCM_ds.save_as(DeDICOMPath)
		#Add Data to Deidentification CSV File
		add = pd.DataFrame([DeCSVData],columns=self.title)
		var_DeCSV_df = var_DeCSV_df.append(add, ignore_index=False)
		var_DeCSV_df = var_DeCSV_df.sort_values(by=['Virtual_PatientName','Virtual_DICOMName'], ascending=True, ignore_index=True)
		return var_DeCSV_df

	
	#Data: CSV File     #Version 3 : Set Image_File_Name from InstanceUID to Flow Numbers('F000001')
	def CSV_Deidentification(self, var_Case_df, var_VirtualCaseName):         #Called by Deidentification Function     #Input a Case CSV Data, VirtualCaseName / return DCMInstanceUIDList
		#read csv
		#df = pd.read_csv(var_CSVpath)  #Version 3: Open the Case csv in Deidentification function -> it is necessary when setting the vitual case name
		var_Case_df = var_Case_df.sort_values(by=['Image_File_Name','Ultrasound_Number'],ascending=True,ignore_index=True)
		#Drop Patient_ID and Full_Image_Path
		var_Case_df.drop(columns='Patient_ID',inplace=True)
		var_Case_df.drop(columns='Full_Image_Path',inplace=True) #Version 3 : drop Full_Image_Path column (no need to record)
		
		DCMInstanceUIDList = []  #Version 3 : index -> decode new ImageName
		for index in range(0,len(var_Case_df)):
			#rename Patient_Flow_Number ,Image_File_Name
			var_Case_df.loc[index, "Patient_Flow_Number"] = var_VirtualCaseName  #Version 3
			if str(var_Case_df.loc[index, "Image_File_Name"]) not in DCMInstanceUIDList:  #Version 3
				DCMInstanceUIDList += [ str(var_Case_df.loc[index, "Image_File_Name"]) ]
			DCMIndex = DCMInstanceUIDList.index( str(var_Case_df.loc[index, "Image_File_Name"]) )
			var_Case_df.loc[index, "Image_File_Name"] = 'F'+ '0' * (6-len(str(DCMIndex+1))) + str(DCMIndex+1)  #Version 3
			
		var_Case_df = var_Case_df[self.groups] #Version 3 : Sort column titles sequence
		
		var_CaseDeCSVpath=os.path.join(self.DeCSVDB_path, var_VirtualCaseName+'.csv')
		var_Case_df.to_csv(var_CaseDeCSVpath, mode='w', header=True,index=False)
		return DCMInstanceUIDList  #Version 3


	#Data: JPG Image (ROI/Full) #Version 3 : Combine Crop_Deidentification & Full_Deidentification to one function
	def JPG_Deidentification(self, var_JPGPath, var_DeJPGPath, var_DCMInstanceUIDList):      #Called by Deidentification Function    
		shutil.copytree(var_JPGPath, var_DeJPGPath)  #Create a new folder and copy all the files of the old folder to the new one #return new folder path
		
		for FileName in os.listdir(var_DeJPGPath):  #Version 3 : the JPG file names sholud be rename. (InstanceUID -> Flow number)
			InstanceUID = FileName[:FileName.index('_')]
			DCMIndex = var_DCMInstanceUIDList.index(InstanceUID)
			NewJPGName = 'F'+ '0' * (6-len(str(DCMIndex+1))) + str(DCMIndex+1)+ FileName[FileName.index('_'):]
			os.rename(os.path.join(var_DeJPGPath, FileName), os.path.join(var_DeJPGPath, NewJPGName))
	
	"""	
	#Version 2
	#Data: Cropped Image (ROI) 
	def Crop_Deidentification(self, var_Croppath, var_CaseFile_name):                        #Called by Deidentification Function
		var_DeCroppath=self.DeCropDB_path+'/'+var_CaseFile_name
		if os.path.exists(var_DeCroppath):
			shutil.rmtree(var_DeCroppath)
		shutil.copytree(var_Croppath,var_DeCroppath)

	#Data: Full Image 
	def Full_Deidentification(self, var_Fullpath, var_CaseFile_name):                        #Called by Deidentification Function
		var_DeFullpath=self.DeFullDB_path+'/'+var_CaseFile_name
		if os.path.exists(var_DeFullpath):
			shutil.rmtree(var_DeFullpath)
		shutil.copytree(var_Fullpath,var_DeFullpath)
	"""	
		
	def Deidentification(self):  #Version 3 : Use CSV file to do deientification case by case & patient flow numbers are definded in Deidentification function      #Called by Deidentify_Action Function(in MainWindow Class)
		#Note: Delete the previous deidentification work first to make sure the data in deidentication folder is corrected! 
		#Initialization
		Deidentify.__init__(Deidentify)
		#Check the previous Database.path_Deidentify
		if len(os.listdir(Database.path_Deidentify))!=0: #Version 3 : if deidentified data is existed, remove all the previous data
			shutil.rmtree(Database.path_Deidentify)
		#Create DeidentifiedDB Folder
		if not os.path.exists(Database.path_Deidentify):
			os.mkdir(Database.path_Deidentify)
		if not os.path.exists(self.DeDICOMDB_path):  #'1. DICOM File'
			os.mkdir(self.DeDICOMDB_path)
		if not os.path.exists(self.DeCSVDB_path):    #'2. CSV File'
			os.mkdir(self.DeCSVDB_path)
		if not os.path.exists(self.DeCropDB_path):   #'3. Cropped US Image'
			os.mkdir(self.DeCropDB_path)
		if not os.path.exists(self.DeFullDB_path):   #'4. Full US Image'
			os.mkdir(self.DeFullDB_path)
		
		CaseList = []   #Patient ID
		#CaseList
		for FileName in os.listdir(Database.path_OriginalDB):
			if '.csv' in FileName:
				CaseList += [FileName[:-4]]
		
		
		#Create or Check DCM DCM_Deidentify.csv
		DeCSVPath = os.path.join(self.DeDICOMDB_path,'DCM_Lable.csv')  #DeCSVPath: '/A4_Final_AI_CAD_System/Anns AI Windows/Deidentification/1. DICOM File/DCM_Lable.csv'
		if not os.path.exists(DeCSVPath):
			df = pd.DataFrame([], columns=self.title)
			df.to_csv(DeCSVPath, mode='w', header=True, index=False)
		#Read DCM_Deidentify.csv
		df = pd.read_csv(DeCSVPath)
		#df = df.sort_values(by=['Virtual_PatientName','Virtual_DICOMName'], ascending=True, ignore_index=True)
		
	
		#DICOMList
		CaseCount = 0
		for PID in CaseList: #Only Deidentify the DCM with Labeled Data->to be sure the DCM can be opened by pydicom
			#Case Setting: CaseCSVPath, DICOM Data in PACS, Virtual Case Name 
			#Case CSV Data
			CaseCSVPath = os.path.join(Database.path_OriginalDB, PID+'.csv')
			Case_df = pd.read_csv(CaseCSVPath)
			if len(Case_df)==0: #if Case_df is empty, pass this loop  #Reference: https://www.geeksforgeeks.org/break-continue-and-pass-in-python/
				continue
			#DICOM Data
			InstanceUIDList, DICOMDataList = Find.PACS_dicom_return(Find, PID)  #Return InstanceUIDList, DICOMDataList
			#Virtual Case Name 
			CaseCount += 1
			Virtual_CaseName = 'P_' + '0'*(4-len(str(CaseCount)))+str(CaseCount)

			
			#Work with Case CSV File Deidentification (Patient ID & Full Image Path(Delete column), Case Name(Change to Anonymous Case Name 'P_0001'), Image File Name(Change SOPInstanceUID to Sequence File Name 'F000001'))
			DCMInstanceUIDList = self.CSV_Deidentification(self, Case_df, Virtual_CaseName)

			#Work with Crop Image Name (Add Anonymous Case Name 'P_0001' to the frount, Change SOPInstanceUID to Sequence File Name 'F000001')
			CaseCropFolderPath=os.path.join(Database.path_Crop_Image, PID)
			DeCaseCropFolderPath=os.path.join(self.DeCropDB_path, Virtual_CaseName)
			self.JPG_Deidentification(self, CaseCropFolderPath, DeCaseCropFolderPath, DCMInstanceUIDList)
			
			#Work with Full Image Name (Add Anonymous Case Name 'P_0001' to the frount, Change SOPInstanceUID to Sequence File Name 'F000001')
			CaseFullFolderPath=os.path.join(Database.path_Full_Image, PID)
			DeCaseFullFolderPath=os.path.join(self.DeFullDB_path, Virtual_CaseName)
			self.JPG_Deidentification(self, CaseFullFolderPath, DeCaseFullFolderPath, DCMInstanceUIDList)
			
			#Work with DICOM File Deidentification (Pixel Data, Tags-SOPInstanceUID/StudyInstanceUID/SeriesInstanceUID)
			CaseDeDCMFolderPath = os.path.join(self.DeDICOMDB_path ,Virtual_CaseName)
			if not os.path.exists(CaseDeDCMFolderPath):
				os.mkdir(CaseDeDCMFolderPath)
			for i, DCMInstanceUID in enumerate(DCMInstanceUIDList):
				VirtualDCMName = 'F' + '0'*(6-len(str(i+1))) + str(i+1)
				ds = DICOMDataList[InstanceUIDList.index(DCMInstanceUID)]
				df = self.DCMTag_Deidentification(self, ds, Virtual_CaseName, VirtualDCMName, df)
				
		#Save 'DCM_Lable.csv' File & Show finished massage
		df = df.sort_values(by=['Virtual_PatientName', 'Virtual_DICOMName'], ascending=True, ignore_index=True)
		df.to_csv(DeCSVPath, mode='w', header=True,index=False)	
		mWarning=messagebox.showwarning(title='Warning Window',message='The Deidentifying Work is finished!')
		return


class Label:              #Label Object: an action of Label button
	def __init__(self):                                        #Called by __init__ Function(in MainWindow Class), set_Label_windows Function
		LabelPage.__init__(LabelPage)
		AITool.__init__(AITool)
		Count.__init__(Count)
		
		#the existed US data in CSV file (USBoundary: US Corner)(原始座標)
		#self.X0=0             #Setting: Crop Function 
		#self.Y0=0
		#self.X1=0
		#self.Y1=0
		
		#the existed ROI data in CSV file (ROIBoundary: ROI info)
		self.ROI_X0_L=0       #Setting: set_Label_windows Function -> Purpose: Reset Case.ROIBoundary
		self.ROI_Y0_L=0
		self.ROI_Weight_L=0
		self.ROI_Height_L=0
		self.ROI_X0_R=0
		self.ROI_Y0_R=0
		self.ROI_Weight_R=0
		self.ROI_Height_R=0
		
		#the present ROI info(原始座標)
		#self.ROI_X0=0         #Setting: enter(event) Function 
		#self.ROI_Y0=0
		#self.ROI_W=0
		#self.ROI_H=0
		
		#the mouse info
		#self.refPt=[]                 #Setting: enter(event) Function / Clearing: clear(event) Function
		
		#the patient data for labeling
		self.VarFullSize=''           #Setting: Save_label Function 
		self.VarFullPath=''           #Setting: Save_label Function
		self.VarROIStartLocation=''   #Setting: Save_label Function (相對座標)
		self.VarROIImageSize=''       #Setting: Save_label Function
		self.VarCropPath=''           #Setting: Save_label Function
	
			
	def Point(self, Point1, Point2):                           #Called by enter Function                #Reset refPt(up left to down right): input refPt / return refPt   
		X_coordinate=[Point1[0], Point2[0]]
		Y_coordinate=[Point1[1], Point2[1]]
		
		X_coordinate.sort()
		Y_coordinate.sort()
			
		return [(X_coordinate[0], Y_coordinate[0]), (X_coordinate[1], Y_coordinate[1])]#start : up left / end : down right
	
	def enter(self, event):                                    #Called by Crop Function
		#Global Varibles Initial Setting
		LabelPage.ROI_X0, LabelPage.ROI_Y0, LabelPage.ROI_W, LabelPage.ROI_H = 0, 0, 0, 0
		
		#Setting Original refPt
		if len(LabelPage.refPt)<2: #only when refPt list is not filled, enter the mouse event into the refPt list
			if event.x-10 < LabelPage.X1 and event.x - 10 >= LabelPage.X0 and event.y-10 < LabelPage.Y1 and event.y - 10 >= LabelPage.Y0:
				LabelPage.refPt.append((event.x-10, event.y-10))	#refPt=[] -> refPt=[(event.x-10, event.y-10)]
		
		#Deal with refPt and show up ROI
		if len(LabelPage.refPt)==2: 
			#Setting Correct refPt
			LabelPage.refPt = self.Point(LabelPage.refPt[0],LabelPage.refPt[1])
			#Re-show up the ROI
			MainPage.canvas.coords(MainPage.rectangle3,(10 + LabelPage.refPt[0][0], 10 + LabelPage.refPt[0][1], 10 + LabelPage.refPt[1][0], 10 + LabelPage.refPt[1][1]))
			
			#Setting ROI information Variables
			LabelPage.ROI_X0 = LabelPage.refPt[0][0]
			LabelPage.ROI_Y0 = LabelPage.refPt[0][1]
			LabelPage.ROI_W = LabelPage.refPt[1][0] - LabelPage.refPt[0][0]
			LabelPage.ROI_H = LabelPage.refPt[1][1] - LabelPage.refPt[0][1]	
			MainPage.lROILocation.config(text=' (X0,Y0):'+'('+str(LabelPage.ROI_X0)+','+str(LabelPage.ROI_Y0)+')'+' , '+'W:'+ str(LabelPage.ROI_W)+' , '+'H:'+str(LabelPage.ROI_H))
			print(LabelPage.ROI_X0, LabelPage.ROI_Y0, LabelPage.ROI_W, LabelPage.ROI_H)
			
		print('enter', LabelPage.refPt)
	
	def clear(self, event):                                    #Called by Crop Function
		LabelPage.refPt=[]
		LabelPage.ROI_X0, LabelPage.ROI_Y0, LabelPage.ROI_W, LabelPage.ROI_H = 0, 0, 0, 0
		MainPage.canvas.coords(MainPage.rectangle3,(10, 10, 10, 10))
		MainPage.lROILocation.config(text=' (X0,Y0):'+'('+str(LabelPage.ROI_X0)+','+str(LabelPage.ROI_Y0)+')'+' , '+'W:'+ str(LabelPage.ROI_W)+' , '+'H:'+str(LabelPage.ROI_H))
		#Clear Heat Map
		if Count.HeatmapCount==0:
			img = Image.fromarray(Case.ImageArraywithMask.astype(np.uint8),'RGB')
			MainPage.photo = ImageTk.PhotoImage(img)
			MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
		print('clear',LabelPage.refPt)
	
	def Square(self):                                          #Called by Save_label Function           #Reset ROI Information Variables: input ROI_X0,ROI_Y0,ROI_W,ROI_H / return ROI_X0,ROI_Y0,ROI_W,ROI_H   
		if LabelPage.ROI_X0==0 and LabelPage.ROI_Y0==0 and LabelPage.ROI_W==0 and LabelPage.ROI_H==0:
			LabelPage.refPt=[]
			return
		
		print(LabelPage.X0, LabelPage.Y0, LabelPage.X1, LabelPage.Y1)
		#Fat Rectangle ROI
		if LabelPage.ROI_W > LabelPage.ROI_H:
			#the W & H difference
			edge_difference = LabelPage.ROI_W - LabelPage.ROI_H
			edge1 = int(edge_difference/3)
			edge2 = edge_difference - edge1
			
			#Original Four Side Bounding
			Up_bounding = LabelPage.ROI_Y0 - edge1
			Down_bounding = LabelPage.ROI_Y0 + LabelPage.ROI_H + edge2
			Left_bounding = LabelPage.ROI_X0
			Right_bounding = LabelPage.ROI_X0 + LabelPage.ROI_W
			
			#Reset Down Bounding
			if Up_bounding < LabelPage.Y0:
				need = LabelPage.Y0 - (LabelPage.ROI_Y0 - edge1)
				Up_bounding = LabelPage.Y0
				if Down_bounding + need < LabelPage.Y1 + 1:
					Down_bounding = Down_bounding+need
				else:
					Down_bounding = LabelPage.Y1
			
			#Reset Up Bounding		
			if Down_bounding > LabelPage.Y1:
				need=(LabelPage.ROI_Y0 +LabelPage.ROI_H + edge2) - LabelPage.Y1
				Down_bounding = LabelPage.Y1
				if Up_bounding - need >= LabelPage.Y0:
					Up_bounding = Up_bounding-need
				else:
					Up_bounding = LabelPage.Y0
			
			#Reset ROI Information Variables		
			LabelPage.ROI_X0 = Left_bounding
			LabelPage.ROI_Y0 = Up_bounding
			LabelPage.ROI_H = Down_bounding-Up_bounding+1
			LabelPage.ROI_W = Right_bounding-Left_bounding+1
		
		#Tall Rectangle ROI
		elif LabelPage.ROI_W < LabelPage.ROI_H:
			#the W & H difference
			edge_difference = LabelPage.ROI_H - LabelPage.ROI_W
			edge1=int(edge_difference/2)
			edge2=edge_difference-edge1
			
			#Original Four Side Bounding
			Up_bounding = LabelPage.ROI_Y0
			Down_bounding = LabelPage.ROI_Y0 + LabelPage.ROI_H
			Left_bounding = LabelPage.ROI_X0 - edge1
			Right_bounding = LabelPage.ROI_X0 + LabelPage.ROI_W + edge2
			
			#Reset Right Bounding
			if Left_bounding < LabelPage.X0:
				need = LabelPage.X0 - (LabelPage.ROI_X0 - edge1)
				Left_bounding = LabelPage.X0
				if Right_bounding+need < LabelPage.X1+1:
					Right_bounding = Right_bounding+need
				else:
					Right_bounding = LabelPage.X1
			
			#Reset Left Bounding		
			if Right_bounding > LabelPage.X1:
				need=(LabelPage.ROI_X0 + LabelPage.ROI_W + edge2) - LabelPage.X1
				Right_bounding = LabelPage.X1
				if Left_bounding - need >= LabelPage.X0:
					Left_bounding = Left_bounding - need
				else:
					Left_bounding = LabelPage.X0
			
			#Reset ROI Information Variables		
			LabelPage.ROI_X0=Left_bounding
			LabelPage.ROI_Y0=Up_bounding
			LabelPage.ROI_H=Down_bounding-Up_bounding+1
			LabelPage.ROI_W=Right_bounding-Left_bounding+1
			
		#Reset Mouse Points list
		LabelPage.refPt[0]=(LabelPage.ROI_X0, LabelPage.ROI_Y0)
		LabelPage.refPt[1]=(LabelPage.ROI_X0 + LabelPage.ROI_W, LabelPage.ROI_Y0 + LabelPage.ROI_H)
		print(LabelPage.refPt)
		
		return 


	def MassSize_value(self, v):                               #Called by Label_Window_Show Function    #Change lScale_1
		LabelPage.lScale_1.config(text=v+' cm')

	def Depth_value(self, v):                                  #Called by Label_Window_Show Function    #Change lScale_2
		LabelPage.lScale_2.config(text=v+' cm')

	def Crop(self):                                            #Called by Label_Window_Show Function
		#Check VarTypeUS was Clicked
		if str(LabelPage.VarTypeUS.get())=='':
			MainPage.lROILocation.config(text='')
			mWarning1=messagebox.showwarning(title='Warning Window',message='Please click the NUMBER OF US button first!', parent=LabelPage.LabelWindows)
			return
		
		#Setting X0, Y0, X1, Y1 / Check VarTypeUS Click Correct
		if str(LabelPage.VarTypeUS.get())=='1' and len(Case.USBoundary)==1:
			LabelPage.X0=int(Case.USBoundary[0][0])
			LabelPage.Y0=int(Case.USBoundary[0][1])
			LabelPage.X1=int(Case.USBoundary[0][2])
			LabelPage.Y1=int(Case.USBoundary[0][3])
		elif str(LabelPage.VarTypeUS.get())=='2_Left' and len(Case.USBoundary)==2:
			LabelPage.X0=int(Case.USBoundary[0][0])
			LabelPage.Y0=int(Case.USBoundary[0][1])
			LabelPage.X1=int(Case.USBoundary[0][2])
			LabelPage.Y1=int(Case.USBoundary[0][3])
		elif str(LabelPage.VarTypeUS.get())=='2_Right' and len(Case.USBoundary)==2:
			LabelPage.X0=int(Case.USBoundary[1][0])
			LabelPage.Y0=int(Case.USBoundary[1][1])
			LabelPage.X1=int(Case.USBoundary[1][2])
			LabelPage.Y1=int(Case.USBoundary[1][3])
		else:
			MainPage.lROILocation.config(text='')
			mWarning1=messagebox.showwarning(title='Warning Window',message='The NUMBER OF US is WRONG!', parent=LabelPage.LabelWindows)
			return 
		
		#Reset MainWidow DCM View(Clear Heatmap)
		img = Image.fromarray(Case.ImageArraywithMask.astype(np.uint8),'RGB')
		MainPage.photo = ImageTk.PhotoImage(img)
		MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
		
		#Clear Mouse Event and Patient Report Data
		LabelPage.refPt=[]
		LabelPage.ROI_X0, LabelPage.ROI_Y0, LabelPage.ROI_W, LabelPage.ROI_H = 0, 0, 0, 0
		MainPage.canvas.coords(MainPage.rectangle1,(10, 10, 10, 10)) #2_Left / 1
		MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10)) #2_Right
		MainPage.canvas.coords(MainPage.rectangle3,(10, 10, 10, 10)) #Label
		#Case.Patient=[0,0,0,0,0,0,0,0,LabelPage.VarBIRADS.get(),0,0,0,0,0,0,0,0,0,0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]
		"""
		Case.Patient=[Case.PatientID, Case.FileName, Case.ImageName, Case.DICOMInstance, 0, LabelPage.VarTypeUS.get(), LabelPage.VarSide.get(), LabelPage.VarTissue.get(), LabelPage.VarBIRADS.get(),0, 0, 0, 0, 0, 0,
			str(LabelPage.sSize.get())+' cm', str(LabelPage. sDepth.get())+' cm', LabelPage.VarLesionLocation.get(), self.VarFullSize, self.VarFullPath, self.VarROIStartLocation, self.VarROIImageSize] #Version 2
		"""
		Case.Patient=[Case.PatientID, Case.ImageName, Case.DICOMInstance, 0, LabelPage.VarTypeUS.get(), LabelPage.VarSide.get(), LabelPage.VarTissue.get(), LabelPage.VarBIRADS.get(),0, 0, 0, 0, 0, 0,
			str(LabelPage.sSize.get())+' cm', str(LabelPage. sDepth.get())+' cm', LabelPage.VarLesionLocation.get(), self.VarFullSize, self.VarFullPath, self.VarROIStartLocation, self.VarROIImageSize]  #Version 3 : Remove Case.FileName item
		Find.Change_PInfo(Find, Case.Patient)
		#Reset AI BI-RADS Level----*
		MainPage.C_AIBirads.config(text='0')
		
		#Crop ROI
		MainPage.lROILocation.config(text=' (X0,Y0):'+'('+str(LabelPage.ROI_X0)+','+str(LabelPage.ROI_Y0)+')'+' , '+'W:'+ str(LabelPage.ROI_W)+' , '+'H:'+str(LabelPage.ROI_H))
		MainPage.Window.bind("<Button-1>", self.enter)
		MainPage.Window.bind("<Button-3>", self.clear)
		return
	
	def Save_label(self):		                               #Called by Label_Window_Show Function
		#Reset ROI Information Variables: refPt, ROI_X0, ROI_Y0, ROI_W, ROI_H
		#(self.ROI_X0, self.ROI_Y0, self.ROI_W, self.ROI_H)=self.Size(self.ROI_X0, self.ROI_Y0, self.ROI_W, self.ROI_H)
		self.Square()
		
		#Setting the CSV variables
		if LabelPage.ROI_X0==0 and LabelPage.ROI_Y0==0 and LabelPage.ROI_W==0 and LabelPage.ROI_H==0:
			#Full---------------
			self.VarFullPath=''
			self.VarFullSize=''  
			#Crop---------------
			self.VarCropPath=''
			self.VarROIStartLocation=''
			self.VarROIImageSize=''
					
		else:	
			#Full---------------
			#Setting VarFullPath
			#FullPath=os.path.join(Database.path_Full_Image,Case.FileName)   #Version 2 #'/Users/chulab/Desktop/USDB_test/US_Image_Only/'A226043704'
			FullPath=os.path.join(Database.path_Full_Image,Case.PatientID)   #Version 3 #'/Users/chulab/Desktop/USDB_test/US_Image_Only/'A226043704'
			JPGName=Case.ImageName+'_Full_'+str(LabelPage.VarTypeUS.get())+'.jpg'   #F000001_Full_2_Left.jpg
			self.VarFullPath=os.path.join(FullPath,JPGName)                         #'/Users/chulab/Desktop/USDB_test/US_Image_Only/'A226043704/F000001_Full_2_Left.jpg'
			#Setting VarFullSize
			self.VarFullSize='H:'+str(LabelPage.Y1+1-LabelPage.Y0)+'x'+'W:'+str(LabelPage.X1+1-LabelPage.X0)
			print(self.VarFullPath)
			#Crop---------------
			#Setting VarCropPath
			#CropPath=os.path.join(Database.path_Crop_Image,Case.FileName)   #Version 2 #'/Users/chulab/Desktop/USDB_test/US_Image_Only/'A226043704'
			CropPath=os.path.join(Database.path_Crop_Image,Case.PatientID)   #Version 3 #'/Users/chulab/Desktop/USDB_test/US_Image_Only/'A226043704'
			JPGName=Case.ImageName+'_Crop_'+str(LabelPage.VarTypeUS.get())+'.jpg'    #F000001_Crop_2_Left.jpg
			self.VarCropPath=os.path.join(CropPath,JPGName)                          #'/Users/chulab/Desktop/USDB_test/US_Image_Only/'A226043704/F000001_Crop_2_Left.jpg'
			#Setting VarROIStartLocation, VarROIImageSize
			self.VarROIStartLocation='X:'+str(LabelPage.ROI_X0-LabelPage.X0)+'Y:'+str(LabelPage.ROI_Y0-LabelPage.Y0)
			self.VarROIImageSize='W:'+str(LabelPage.ROI_W)+'H:'+str(LabelPage.ROI_H)
			                           

		#If not click Patient_Label(Case.Patient) element would be ''
		"""
		Case.Patient=[Case.PatientID, Case.FileName, Case.ImageName, Case.DICOMInstance, 0,
			LabelPage.VarTypeUS.get(), LabelPage.VarSide.get(), LabelPage.VarTissue.get(), LabelPage.VarBIRADS.get(),
			0, 0, 0, 0, 0, 0,
			str(LabelPage.sSize.get())+' cm', str(LabelPage. sDepth.get())+' cm', LabelPage.VarLesionLocation.get(), self.VarFullSize, self.VarFullPath, self.VarROIStartLocation, self.VarROIImageSize]  #Version 2
		"""
		Case.Patient=[Case.PatientID, Case.ImageName, Case.DICOMInstance, 0,
			LabelPage.VarTypeUS.get(), LabelPage.VarSide.get(), LabelPage.VarTissue.get(), LabelPage.VarBIRADS.get(),
			0, 0, 0, 0, 0, 0,
			str(LabelPage.sSize.get())+' cm', str(LabelPage. sDepth.get())+' cm', LabelPage.VarLesionLocation.get(), self.VarFullSize, self.VarFullPath, self.VarROIStartLocation, self.VarROIImageSize] #Version 3 : Remove Case.FileName item
		
		#Check Label Work is finished
		if '' in Case.Patient:
			mWarning=messagebox.showwarning(title='Warning Window',message='The Label Work is not completed!', parent=LabelPage.LabelWindows)
		else:
			print('Finished!')
			#Save Full Image JPEG----------------------------------------------------------------------
			#Create Full Image File / Set Case Full Image Path
			if os.path.exists(FullPath)==False:
				os.mkdir(FullPath)
			#Save a specific side of US full image to a JPG file	
			Image_array_full=Case.ImageArray[LabelPage.Y0:LabelPage.Y1+1,LabelPage.X0:LabelPage.X1+1,:]
			img_full=Image.fromarray(Image_array_full,'RGB')
			img_full.save(self.VarFullPath,'JPEG')
			
			#Save Cropped Image JPEG-------------------------------------------------------------------
			#Create Cropped Image File / Set Case Cropped Image Path
			if os.path.exists(CropPath)==False:
				os.mkdir(CropPath)
			#Get a specific side of US cropped image to a JPG file
			Image_array_crop=Case.ImageArray[LabelPage.ROI_Y0 : LabelPage.ROI_Y0+LabelPage.ROI_H, LabelPage.ROI_X0 : LabelPage.ROI_X0+LabelPage.ROI_W, :]
			img_crop=Image.fromarray(Image_array_crop,'RGB')
			img_crop.save(self.VarCropPath,'JPEG')

			
			#Save CSV----------------------------------------------------------------------------------
			#Previous CSV Data : Case.CaseLabelData  
			#df = pd.read_csv(Case.CSVPath)      
			#Version 3: Create CSV File till the first label work be saved (Find.Find_file)
			if not os.path.exists(Case.CSVPath): 
				df=pd.DataFrame([], columns=Find.Groups)
				df.to_csv(Case.CSVPath, mode='w', header=True, index=False)
				Case.CaseLabelData = pd.read_csv(Case.CSVPath)
			 
			#Drop the same DataFrame
			for i in range(0,len(Case.CaseLabelData)):
				if str(Case.CaseLabelData['Image_File_Name'][i])==Case.ImageName and str(Case.CaseLabelData['Ultrasound_Number'][i])==str(LabelPage.VarTypeUS.get()):
					Case.CaseLabelData.drop(index=i,inplace=True)
			
			#New adding DataFrame
			add_item = pd.DataFrame([Case.Patient],columns=Find.Groups)
			#Save CSV File  #Version 3 : add new DataFrame to Case.CaseLabelData -> sort Case.CaseLabelData -> save Case.CaseLabelData
			Case.CaseLabelData = Case.CaseLabelData.append(add_item, ignore_index=False)
			Case.CaseLabelData = Case.CaseLabelData.sort_values(by=['Image_File_Name','Ultrasound_Number'], ascending=True, ignore_index=True)
			Case.CaseLabelData.to_csv(Case.CSVPath, mode='w', header=True,index=False) #After Drop DataFrame (Necessary)
			
			#Reset df       #Version 3 : no need to sort Case.CaseLabelData again
			Case.CaseLabelData = pd.read_csv(Case.CSVPath)
			
			#Reset window Objects----------------------------------------------------------------------
			MainPage.canvas.coords(MainPage.rectangle3,(10 + LabelPage.ROI_X0, 10 + LabelPage.ROI_Y0, 10 + LabelPage.ROI_X0 + LabelPage.ROI_W, 10 + LabelPage.ROI_Y0 + LabelPage.ROI_H))
			MainPage.lROILocation.config(text=' (X0,Y0):'+'('+str(LabelPage.ROI_X0)+','+str(LabelPage.ROI_Y0)+')'+' , '+'W:'+ str(LabelPage.ROI_W)+' , '+'H:'+str(LabelPage.ROI_H))
			
			Find.Change_PInfo(Find, Case.Patient)

		print(Case.Patient)
		return 
	
	def Clear_info(self):                                      #Called by Label_Window_Show Function
		#Tkinter object
		LabelPage.VarSide.set('')
		LabelPage.VarTissue.set('')
		LabelPage.VarBIRADS.set('')
		LabelPage.VarTypeUS.set('')
		LabelPage.VarLesionLocation.set('')
		
		LabelPage.sSize.set(0)
		LabelPage.sDepth.set(0)
		
		LabelPage.lScale_1.config(text='0.00 cm')
		LabelPage.lScale_2.config(text='0.00 cm')
		
		LabelPage.rRight.deselect()
		LabelPage.rLeft.deselect()
		
		LabelPage.rFat.deselect()
		LabelPage.rFibro.deselect()
		LabelPage.rHet.deselect()
		
		LabelPage.rC1.deselect()
		LabelPage.rC2.deselect()
		LabelPage.rC3.deselect()
		LabelPage.rC4.deselect()
		LabelPage.rC5.deselect()
		
		LabelPage.rOne.deselect()
		LabelPage.rLTwo.deselect()
		LabelPage.rRTwo.deselect()
		
		LabelPage.rQI.deselect()
		LabelPage.rQII.deselect()
		LabelPage.rQIII.deselect()
		LabelPage.rQIV.deselect()
		
		
		#Variables 
		self.VarFullSize=''
		self.VarFullPath=''
		self.VarROIStartLocation=''
		self.VarROIImageSize=''
		
		LabelPage.refPt=[]
		MainPage.canvas.coords(MainPage.rectangle3,(10, 10, 10, 10)) #Label
		MainPage.lROILocation.config(text='')
		MainPage.Window.unbind("<Button-1>")
		MainPage.Window.unbind("<Button-3>")
		#Case.Patient=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]
		Case.Patient=[0,0,0,0, 0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0] #Version 3
		Find.Change_PInfo(Find, Case.Patient)
		MainPage.C_AIBirads.config(text='0')
		
		LabelPage.ROI_X0, LabelPage.ROI_Y0, LabelPage.ROI_W, LabelPage.ROI_H = 0, 0, 0, 0
		LabelPage.X0, LabelPage.Y0, LabelPage.X1, LabelPage.Y1 = 0, 0, 0, 0
		
		#Reset MainWidow DCM View(Clear Heatmap)
		img = Image.fromarray(Case.ImageArraywithMask.astype(np.uint8),'RGB')
		MainPage.photo = ImageTk.PhotoImage(img)
		MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
	
	def set_Label_windows(self):                               #Called by Label_Window_Show Function
		#Label_windows
		if LabelPage.LabelWindows!='':
			LabelPage.LabelWindows.destroy()
		Label.__init__(Label)
		
		#window
		#Reset: df_item, ROI_X0_L, ROI_Y0_L, ROI_Weight_L, ROI_Height_L, ROI_X0_R, ROI_Y0_R, ROI_Weight_R, ROI_Height_R
		Case.CSVDataItem=[]
		for i in range(0,len(Case.CaseLabelData)):
			if str(Case.CaseLabelData['Image_File_Name'][i])==str(Case.ImageName):
				if str(Case.CaseLabelData['Ultrasound_Number'][i])=='2_Left' or str(Case.CaseLabelData['Ultrasound_Number'][i])=='1':
					self.ROI_X0_L, self.ROI_Y0_L = Find.get_colon_location_in_a_string(Find, str(Case.CaseLabelData['ROI_Start_Location'][i]))
					self.ROI_Weight_L, self.ROI_Height_L = Find.get_colon_location_in_a_string(Find, str(Case.CaseLabelData['ROI_Image_Size'][i]))
					#print('L:',ROI_X0_L,ROI_Y0_L,ROI_Weight_L,ROI_Height_L)
				elif str(Case.CaseLabelData['Ultrasound_Number'][i])=='2_Right':
					self.ROI_X0_R, self.ROI_Y0_R = Find.get_colon_location_in_a_string(Find, str(Case.CaseLabelData['ROI_Start_Location'][i]))
					self.ROI_Weight_R, self.ROI_Height_R = Find.get_colon_location_in_a_string(Find, str(Case.CaseLabelData['ROI_Image_Size'][i]))	
					#print('R:',ROI_X0_R,ROI_Y0_R,ROI_Weight_R,ROI_Height_R)
				Case.CSVDataItem=Case.CSVDataItem+[i]
				
		
		#ROI_Boundary & showup ROI Defloat(canvas)
		Case.ROIBoundary=[]
		if len(Case.USBoundary)==1:
			Case.ROIBoundary=Case.ROIBoundary+[[int(self.ROI_X0_L+Case.USBoundary[0][0]),int(self.ROI_Y0_L+Case.USBoundary[0][1]),int(self.ROI_Weight_L),int(self.ROI_Height_L)]] #[DICOM X 座標, DICOM Y 座標, ROI Weight, ROI Height]
		elif len(Case.USBoundary)==2:
			if self.ROI_X0_L!=0 or self.ROI_Y0_L!=0 or self.ROI_Weight_L!=0 or self.ROI_Height_L!=0:
				Case.ROIBoundary=Case.ROIBoundary+[[int(self.ROI_X0_L+Case.USBoundary[0][0]),int(self.ROI_Y0_L+Case.USBoundary[0][1]),int(self.ROI_Weight_L),int(self.ROI_Height_L)]]
			if self.ROI_X0_R!=0 or self.ROI_Y0_R!=0 or self.ROI_Weight_R!=0 or self.ROI_Height_R!=0:
				Case.ROIBoundary=Case.ROIBoundary+[[int(self.ROI_X0_R+Case.USBoundary[1][0]),int(self.ROI_Y0_R+Case.USBoundary[1][1]),int(self.ROI_Weight_R),int(self.ROI_Height_R)]]
		
		if len(Case.ROIBoundary)==1:
			MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3])) #rectangle1: 1 or 2_Left
			MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10))		
		elif len(Case.ROIBoundary)==2:	
			MainPage.canvas.coords(MainPage.rectangle1,(10+Case.ROIBoundary[0][0], 10+Case.ROIBoundary[0][1], 10+Case.ROIBoundary[0][0]+Case.ROIBoundary[0][2], 10+Case.ROIBoundary[0][1]+Case.ROIBoundary[0][3]))
			MainPage.canvas.coords(MainPage.rectangle2,(10+Case.ROIBoundary[1][0], 10+Case.ROIBoundary[1][1], 10+Case.ROIBoundary[1][0]+Case.ROIBoundary[1][2], 10+Case.ROIBoundary[1][1]+Case.ROIBoundary[1][3])) #rectangle1: 2_Right
		MainPage.canvas.coords(MainPage.rectangle3,(10, 10, 10, 10)) #Label
		
		MainPage.lROILocation.config(text='')
		MainPage.Window.unbind("<Button-1>")  #取消綁定
		MainPage.Window.unbind("<Button-3>")
		
		#Change Patient Report
		#Case.Patient=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]
		Case.Patient=[0,0,0,0, 0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]  #Version 3
		Find.Change_PInfo(Find, Case.Patient)
		MainPage.C_AIBirads.config(text='0')
		
		#Reset MainWidow DCM View(Clear Heatmap)
		img = Image.fromarray(Case.ImageArraywithMask.astype(np.uint8),'RGB')
		MainPage.photo = ImageTk.PhotoImage(img)
		MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
		return
	
	
	def Label_Window_Show(self):                               #Called by Label_Action Function(in MainWindow Class)
		#Check the csv DataFrame exists
		if Case.PatientID=='' or Case.ImageName=='':    #Version 3 : Case.FileName->Case.PatientID
			mWarning=messagebox.showwarning(title='Warning Window',message='Please input a correct Case Name!')
			return
		
		#canvas
		MainPage.canvas.coords(MainPage.rectangle1,(10, 10, 10, 10)) #2_Left / 1
		MainPage.canvas.coords(MainPage.rectangle2,(10, 10, 10, 10)) #2_Right
		MainPage.canvas.coords(MainPage.rectangle3,(10, 10, 10, 10)) #Label
		
		#Change Patient Report
		#Case.Patient=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]
		Case.Patient=[0,0,0,0, 0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,'/Users/chulab/Desktop/USDB_tset/US_Image_Only/0',0,0]  #Version 3
		Find.Change_PInfo(Find, Case.Patient)
		
		#Label_windows-------------------------------------------------------------------------------------------------------------------------------
		LabelPage.LabelWindows = tk.Toplevel(MainPage.Window)
		LabelPage.LabelWindows.title('Label Window')
		LabelPage.LabelWindows.geometry('450x530')#uint:('widthxhight') 
		LabelPage.LabelWindows.resizable(0,0)
		LabelPage.LabelWindows.protocol('WM_DELETE_WINDOW', self.set_Label_windows)
		
		#font decision
		f_title = font.Font(family="Helvetica", size=14, weight='bold')#16
		f_content = font.Font(family="Helvetica", size=12)
		f_label_item = font.Font(family="Helvetica", size=10, weight='bold', underline=1)
		f_label_content = font.Font(family="Helvetica", size=10)#12
		f_button1 = font.Font(family="Helvetica", size=10)
		f_button2 = font.Font(family="Helvetica", size=12, weight='bold')

		#layout:frame
		#Object(width=,height=) #Unit: words
		#grid(row:列橫,column:行直)#place(x:width橫坐標,y:height直座標)
		#entry----------------------------------------------------------------
		LabelPage.EntryFrame=tk.Frame(LabelPage.LabelWindows)

		#entry: entry patient file name and image(auto find image) 
		LabelPage.lPatient = tk.Label(LabelPage.EntryFrame, text='Patient', font=f_title, anchor='w').grid(row=0, column=0, columnspan=5, pady=3,sticky='w')
		
		LabelPage.T_FileName = tk.Label(LabelPage.EntryFrame, text='Patient ID:',font=f_content, anchor='w').grid(row=1, column=0, columnspan=6, padx=5, pady=2,sticky='w')  #text='Case Name:'
		LabelPage.C_FileName = tk.Label(LabelPage.EntryFrame, text=Case.PatientID,font=f_content, anchor='w')  #Version 3 : Case.FileName->Case.PatientID
		LabelPage.C_FileName.grid(row=1, column=7, columnspan=5, padx=5, pady=2,sticky='w')
		LabelPage.T_DICOMFileName = tk.Label(LabelPage.EntryFrame, text='DICOM Instance UID:',font=f_content, anchor='w').grid(row=2, column=0, columnspan=6, padx=5, pady=2,sticky='w') #text='DICOM File Name:'
		LabelPage.C_DICOMFileName = tk.Label(LabelPage.EntryFrame, text=Case.ImageName[0:11]+'...'+Case.ImageName[-6:],font=f_content, anchor='w') #Version2 : Case.ImageName
		LabelPage.C_DICOMFileName.grid(row=2, column=7, columnspan=5, padx=5, pady=2,sticky='w')
		
		LabelPage.EntryFrame.pack(side='top', anchor='nw', fill='x', expand='no')
		
		#lesion feature-----------------------------------------------------------
		LabelPage.LabelFrame=tk.Frame(LabelPage.LabelWindows)

		#lesion feature:label
		LabelPage.lLabel = tk.Label(LabelPage.LabelFrame, text='Lesion Features', font=f_title, anchor='w').grid(row=0, column=0, columnspan=5, pady=3,sticky='w')

		LabelPage.lItem1_r0c0 = tk.Label(LabelPage.LabelFrame, text='Breast Side:', font=f_label_item,anchor='w').grid(row=1, column=0, columnspan=10, padx=10,sticky='w')
		LabelPage.VarSide = tk.StringVar()
		LabelPage.rRight = tk.Radiobutton(LabelPage.LabelFrame, text='Right', font=f_label_content, variable=LabelPage.VarSide, value='Right', anchor='w')
		LabelPage.rLeft = tk.Radiobutton(LabelPage.LabelFrame, text='Left', font=f_label_content, variable=LabelPage.VarSide, value='Left', anchor='w')
		LabelPage.rRight.grid(row=2, column=0, columnspan=10, padx=10,sticky='w')
		LabelPage.rLeft.grid(row=3, column=0, columnspan=10, padx=10,sticky='w')

		LabelPage.lItem2_r1c0 = tk.Label(LabelPage.LabelFrame, text='Tissue Composition:', font=f_label_item,anchor='w').grid(row=4, column=0, columnspan=10, padx=10, sticky='w')
		LabelPage.VarTissue = tk.StringVar()
		LabelPage.rFat = tk.Radiobutton(LabelPage.LabelFrame, text='Homogeneous-Fat', font=f_label_content,variable=LabelPage.VarTissue, value='Homogeneous-Fat', anchor='w')
		LabelPage.rFibro = tk.Radiobutton(LabelPage.LabelFrame, text='Homogeneous-Fibroglandular', font=f_label_content,variable=LabelPage.VarTissue, value='Fibroglandular', anchor='w')
		LabelPage.rHet = tk.Radiobutton(LabelPage.LabelFrame, text='Heterogeneous', font=f_label_content,variable=LabelPage.VarTissue, value='Heterogeneous', anchor='w')
		LabelPage.rFat.grid(row=5, column=0, columnspan=10, padx=10,sticky='w')
		LabelPage.rFibro.grid(row=6, column=0, columnspan=10, padx=10,sticky='w')
		LabelPage.rHet.grid(row=7, column=0, columnspan=10, padx=10,sticky='w')

		LabelPage.lItem3_r2c0 = tk.Label(LabelPage.LabelFrame, text='BI-RADS Level:', font=f_label_item,anchor='w').grid(row=8, column=0, columnspan=10, padx=10, sticky='w')
		LabelPage.VarBIRADS = tk.StringVar()
		LabelPage.rC1 = tk.Radiobutton(LabelPage.LabelFrame, text='Category 1', font=f_label_content,variable=LabelPage.VarBIRADS, value='Category 1', anchor='w')
		LabelPage.rC2 = tk.Radiobutton(LabelPage.LabelFrame, text='Category 2', font=f_label_content,variable=LabelPage.VarBIRADS, value='Category 2', anchor='w')
		LabelPage.rC3 = tk.Radiobutton(LabelPage.LabelFrame, text='Category 3', font=f_label_content,variable=LabelPage.VarBIRADS, value='Category 3', anchor='w')
		LabelPage.rC4 = tk.Radiobutton(LabelPage.LabelFrame, text='Category 4', font=f_label_content,variable=LabelPage.VarBIRADS, value='Category 4', anchor='w')
		LabelPage.rC5 = tk.Radiobutton(LabelPage.LabelFrame, text='Category 5', font=f_label_content,variable=LabelPage.VarBIRADS, value='Category 5', anchor='w')
		LabelPage.rC1.grid(row=9, column=0, columnspan=10, padx=10,sticky='w')
		LabelPage.rC2.grid(row=10, column=0, columnspan=10, padx=10,sticky='w')
		LabelPage.rC3.grid(row=11, column=0, columnspan=10, padx=10,sticky='w')
		LabelPage.rC4.grid(row=12, column=0, columnspan=10, padx=10,sticky='w')
		LabelPage.rC5.grid(row=13, column=0, columnspan=10, padx=10,sticky='w')

		#Type of US Image
		LabelPage.lItem13_r0c4 = tk.Label(LabelPage.LabelFrame, text='Number of US:', font=f_label_item,anchor='w').grid(row=1, column=10, columnspan=10, padx=10, sticky='w')
		LabelPage.VarTypeUS = tk.StringVar()
		LabelPage.rOne = tk.Radiobutton(LabelPage.LabelFrame, text='Only One', font=f_label_content,variable=LabelPage.VarTypeUS, value='1', anchor='w')
		LabelPage.rLTwo = tk.Radiobutton(LabelPage.LabelFrame, text='The Left of Two', font=f_label_content,variable=LabelPage.VarTypeUS, value='2_Left', anchor='w')
		LabelPage.rRTwo = tk.Radiobutton(LabelPage.LabelFrame, text='The Right of Two', font=f_label_content,variable=LabelPage.VarTypeUS, value='2_Right', anchor='w')
		LabelPage.rOne.grid(row=2, column=10, columnspan=10, padx=10,sticky='w')
		LabelPage.rLTwo.grid(row=3, column=10, columnspan=10, padx=10,sticky='w')
		LabelPage.rRTwo.grid(row=4, column=10, columnspan=10, padx=10,sticky='w')

		LabelPage.lItem10_r1c3 = tk.Label(LabelPage.LabelFrame, text='Lesion Location:', font=f_label_item,anchor='w').grid(row=5, column=10, columnspan=10, padx=10, sticky='w')
		LabelPage.VarLesionLocation = tk.StringVar()
		LabelPage.rQI = tk.Radiobutton(LabelPage.LabelFrame, text='Quadrant I', font=f_label_content,variable=LabelPage.VarLesionLocation, value='Quadrant I', anchor='w')
		LabelPage.rQII = tk.Radiobutton(LabelPage.LabelFrame, text='Quadrant II', font=f_label_content,variable=LabelPage.VarLesionLocation, value='Quadrant II', anchor='w')
		LabelPage.rQIII = tk.Radiobutton(LabelPage.LabelFrame, text='Quadrant III', font=f_label_content,variable=LabelPage.VarLesionLocation, value='Quadrant III', anchor='w')
		LabelPage.rQIV = tk.Radiobutton(LabelPage.LabelFrame, text='Quadrant IV', font=f_label_content,variable=LabelPage.VarLesionLocation, value='Quadrant IV', anchor='w')
		LabelPage.rQI.grid(row=6, column=10, columnspan=10, padx=10,sticky='w')
		LabelPage.rQII.grid(row=7, column=10, columnspan=10, padx=10,sticky='w')
		LabelPage.rQIII.grid(row=8, column=10, columnspan=10, padx=10,sticky='w')
		LabelPage.rQIV.grid(row=9, column=10, columnspan=10, padx=10,sticky='w')

		LabelPage.lItem11_r2c3 = tk.Label(LabelPage.LabelFrame, text='Lesion Size(Max):', font=f_label_item,anchor='w').grid(row=10, column=10, columnspan=20, padx=10, sticky='w')
		LabelPage.lScale_1 = tk.Label(LabelPage.LabelFrame, text='0.00 cm', font=f_label_content,anchor='e')
		LabelPage.sSize = tk.Scale(LabelPage.LabelFrame, from_=0, to=4, orient=tk.HORIZONTAL, length=200, showvalue=0, tickinterval=1, resolution=0.01, command=self.MassSize_value) #
		LabelPage.sSize.grid(row=11, column=10, columnspan=20, padx=10, sticky='w')#length:pixel
		LabelPage.lScale_1.grid(row=10, column=20, columnspan=10, padx=10, sticky='e')

		LabelPage.lItem12_r3c3 = tk.Label(LabelPage.LabelFrame, text='Lesion Depth:', font=f_label_item,anchor='w').grid(row=12, column=10, columnspan=20, padx=10, sticky='w')
		LabelPage.lScale_2 = tk.Label(LabelPage.LabelFrame, text='0.00 cm', font=f_label_content,anchor='e')
		LabelPage.sDepth = tk.Scale(LabelPage.LabelFrame, from_=0, to=4, orient=tk.HORIZONTAL, length=200, showvalue=0, tickinterval=1, resolution=0.01, command=self.Depth_value) #
		LabelPage.sDepth.grid(row=13, column=10, columnspan=20, padx=10, sticky='w')
		LabelPage.lScale_2.grid(row=12, column=20, columnspan=10, padx=10, sticky='e')

		#Buttom--------------------------------------------------------------------------------------------------
		LabelPage.bCropImage = tk.Button(LabelPage.LabelFrame, text='Crop Image',font=f_button1, command=self.Crop)#
		LabelPage.bCropImage.grid(row=1, column=20,  columnspan=7,sticky='w')
		LabelPage.bSave = tk.Button(LabelPage.LabelFrame, text=' Save  ',font=f_button2, command=self.Save_label)#
		LabelPage.bSave.grid(row=8, column=20,  columnspan=7, padx=5,sticky='w')
		LabelPage.bClear = tk.Button(LabelPage.LabelFrame, text=' Clear ',font=f_button2, command=self.Clear_info)#
		LabelPage.bClear.grid(row=7, column=20,  columnspan=7, padx=5, pady=3, sticky='w')

		LabelPage.LabelFrame.pack(side='top', anchor='nw', fill='both', expand='no')
		LabelPage.LabelWindows.mainloop()
	

class AITool:             #AITool Object: an action of AIClinic, HeatMap, AcceptResult button
	def __init__(self):                                        #Called by __init__ Function(in AITool Class)
		self.AIResult=''         #Setting: AIClinic
		self.Original=''         #Setting: HeatMap
		self.Grad_CAM=''         #Setting: HeatMap
		
	def AIClinic(self):                                        #Called by AIClinic_Action Function(in MainWindow Class)
		AITool.__init__(AITool)
		#self.AIResult=''
		if len(LabelPage.refPt)==2:  #if the Cropped Work is completed
			#Reset ROI Information Variables: refPt, ROI_X0, ROI_Y0, ROI_W, ROI_H
			Label.Square(Label)

			#Reset window Objects----------------------------------------------------------------------
			#Change ROI Bounding Box to square
			MainPage.canvas.coords(MainPage.rectangle3,(10 + LabelPage.ROI_X0, 10 + LabelPage.ROI_Y0, 10 + LabelPage.ROI_X0 + LabelPage.ROI_W, 10 + LabelPage.ROI_Y0 + LabelPage.ROI_H))
			MainPage.lROILocation.config(text=' (X0,Y0):'+'('+str(LabelPage.ROI_X0)+','+str(LabelPage.ROI_Y0)+')'+' , '+'W:'+ str(LabelPage.ROI_W)+' , '+'H:'+str(LabelPage.ROI_H))
			
			#the Cropped Image Numpy Array
			Image_array_crop=Case.ImageArray[LabelPage.ROI_Y0 : LabelPage.ROI_Y0+LabelPage.ROI_H, LabelPage.ROI_X0 : LabelPage.ROI_X0+LabelPage.ROI_W, :] #Input Image
			
			#pyplot.imshow(Image_array_crop, 'gray')
			#pyplot.show()
			
			#Resize the Cropped Image Numpy Array
			Image_crop = Image.fromarray(Image_array_crop) #Numpy.array -> PIL.Image
			Image_crop_resize = Image_crop.resize((96,96), resample=Image.BILINEAR) 
			
			#Normalize the Cropped Image Numpy Array
			jpg_array=np.array(Image_crop_resize)
			jpg_array = ((jpg_array-jpg_array.min())/(jpg_array.max()-jpg_array.min())).astype('float32')
			
			#the Input Data
			Data_Array = np.zeros((1,96,96,3)).astype('float32')
			Data_Array[0] = jpg_array
			#Data_Array[0,:,:,0] = jpg_array
			#Data_Array[0,:,:,1] = jpg_array
			#Data_Array[0,:,:,2] = jpg_array
			
			#Run AI Model and Get Result 
			Max_index=-1    #the result class(the index of the maximum result)
			if os.path.exists(Database.path_AIModel):
				AIModel = load_model(Database.path_AIModel)
				Result=AIModel.predict(Data_Array)   #Predict return an array
				Max_index=np.argmax(Result)
			else:
				mWarning=messagebox.showwarning(title='Warning Window',message='There isn\'t any AI model!', parent=MainPage.Window)
			
			#Settong self.AIResult
			if Max_index==-1: #no model
				self.AIResult = '0'
			elif Max_index==0:
				self.AIResult = 'Category 2'
			elif Max_index==1:
				self.AIResult = 'Category 3'
			elif Max_index==2:
				self.AIResult = 'Category 4'
			#Change MainPage.C_AIBirads
			MainPage.C_AIBirads.config(text=self.AIResult)
			mWarning=messagebox.showwarning(title='Message Window',message='Your AI Analysis is finished!', parent=MainPage.Window)
		else:
			mWarning=messagebox.showwarning(title='Warning Window',message='The Cropped Work is not completed!', parent=MainPage.Window)
		return
	
	def HeatMap(self):                                         #Called by HeatMap_Action Function(in MainWindow Class)
		#Data Preprocessing-------------------------------------------------------------------------
		#Set ROI Shape to Square........................
		#Reset ROI Information Variables: refPt, ROI_X0, ROI_Y0, ROI_W, ROI_H
		if len(LabelPage.refPt)==2:  #if the Cropped Work is completed
			Label.Square(Label)
			
			#Change ROI Bounding Box to square
			MainPage.canvas.coords(MainPage.rectangle3,(10 + LabelPage.ROI_X0, 10 + LabelPage.ROI_Y0, 10 + LabelPage.ROI_X0 + LabelPage.ROI_W, 10 + LabelPage.ROI_Y0 + LabelPage.ROI_H))
			MainPage.lROILocation.config(text=' (X0,Y0):'+'('+str(LabelPage.ROI_X0)+','+str(LabelPage.ROI_Y0)+')'+' , '+'W:'+ str(LabelPage.ROI_W)+' , '+'H:'+str(LabelPage.ROI_H))
			
			#the Cropped Image Numpy Array
			Image_array_crop = Case.ImageArray[LabelPage.ROI_Y0 : LabelPage.ROI_Y0+LabelPage.ROI_H, LabelPage.ROI_X0 : LabelPage.ROI_X0+LabelPage.ROI_W, :] #Input Image
			self.Original = Case.ImageArraywithMask
			self.Grad_CAM = Case.ImageArraywithMask.copy()
			Count.HeatmapCount=0
			
			#print('Original:', Image_array_crop.shape)
			#pyplot.imshow(Image_array_crop) #input: PIL Instance、array-like
			#pyplot.show()
			
			#Set ROI to the model input form........................
			#Resize the Cropped Image Numpy Array
			Image_crop = Image.fromarray(Image_array_crop) #Numpy.array -> PIL.Image
			Image_crop_resize = Image_crop.resize((96,96), resample=Image.BILINEAR)  #resize to model input
			
			#Normalize the Cropped Image Numpy Array
			jpg_array=np.array(Image_crop_resize)
			jpg_array = ((jpg_array-jpg_array.min())/(jpg_array.max()-jpg_array.min())).astype('float32')
			
			#the Input Data
			Data_Array = np.zeros((1,96,96,3)).astype('float32')
			Data_Array[0] = jpg_array
			#Data_Array[0,:,:,0] = jpg_array
			#Data_Array[0,:,:,1] = jpg_array
			#Data_Array[0,:,:,2] = jpg_array

			
			
			#Get Grad-CAM Heat Map-------------------------------------------------------------------------
			#Run AI Model and Get Heat Map 
			if os.path.exists(Database.path_AIModel):
				AIModel = load_model(Database.path_AIModel)
			else: #no model
				mWarning=messagebox.showwarning(title='Warning Window',message='There isn\'t any AI model!', parent=MainPage.Window)
				return
			
			#First, we create a model that maps the input image to the activations of the last conv layer as well as the output predictions
			grad_model = Model([AIModel.inputs], [AIModel.get_layer(index=-4).output, AIModel.output]) #model.get_layer(name=last_conv_layer_name, index=last_conv_layer_index) #-1: Dense, -2:Dropout, -3: GAP, -4: last conv
			
			#Then, we compute the gradient of the top predicted class for our input image with respect to the activations of the last conv layer
			with tf.GradientTape() as tape:
				last_conv_layer_output, preds = grad_model(Data_Array)
				#if pred_index is None:
				pred_index = tf.argmax(preds[0]) #argmax: the index of the maximum number of array
				class_channel = preds[:, pred_index]
				
			#This is the gradient of the output neuron (top predicted or chosen) with regard to the output feature map of the last conv layer
			grads = tape.gradient(class_channel, last_conv_layer_output)

			#This is a vector where each entry is the mean intensity of the gradient over a specific feature map channel
			pooled_grads = tf.reduce_mean(grads, axis=(0, 1, 2))
			
			#We multiply each channel in the feature map array by "how important this channel is" with regard to the top predicted class then sum all the channels to obtain the heatmap class activation
			last_conv_layer_output = last_conv_layer_output[0]
			heatmap = last_conv_layer_output @ pooled_grads[..., tf.newaxis]
			heatmap = tf.squeeze(heatmap)

			#For visualization purpose, we will also normalize the heatmap between 0 & 1
			heatmap = tf.maximum(heatmap, 0) / tf.math.reduce_max(heatmap)
			
			
			#Show up Heat Map------------------------------------------------------------------------------
			# Rescale heatmap to a range 0-255
			heatmap = np.uint8(255 * heatmap.numpy())

			# Use jet colormap to colorize heatmap
			jet = cm.get_cmap("jet")
			# Use RGB values of the colormap
			jet_colors = jet(np.arange(256))[:, :3]
			jet_heatmap = jet_colors[heatmap]

			# Create an image with RGB colorized heatmap
			jet_heatmap = keras.preprocessing.image.array_to_img(jet_heatmap)
			jet_heatmap = jet_heatmap.resize((Image_array_crop.shape[1], Image_array_crop.shape[0])) #resize to original crop image
			jet_heatmap = keras.preprocessing.image.img_to_array(jet_heatmap)

			# Superimpose the heatmap on original image
			superimposed_img = jet_heatmap*0.4 + Image_array_crop  #alpha:0.4
			#print('Grad-CAM:', superimposed_img.shape)
			superimposed_img = keras.preprocessing.image.array_to_img(superimposed_img) #change array to float[0,1] or integer[0,255] #Necessary
			#superimposed_img.save('cam.jpg')
			
			#Show on MainWindow
			self.Grad_CAM[LabelPage.ROI_Y0 : LabelPage.ROI_Y0+LabelPage.ROI_H, LabelPage.ROI_X0 : LabelPage.ROI_X0+LabelPage.ROI_W, :] = np.array(superimposed_img)
			img = Image.fromarray(self.Grad_CAM.astype(np.uint8),'RGB')
			MainPage.photo = ImageTk.PhotoImage(img)
			MainPage.canvas.itemconfig(MainPage.ImageDcm,image=MainPage.photo)
			#print('Grad-CAM:')
			#print(np.array(superimposed_img))
			#pyplot.imshow(superimposed_img)
			#pyplot.show()
		#else:
			#mWarning=messagebox.showwarning(title='Warning Window',message='The Cropped Work is not completed!', parent=MainPage.Window)
		return
	
	def AcceptResult(self):                                    #Called by Accept_Action Function(in MainWindow Class)
		if self.AIResult=='':
			mWarning=messagebox.showwarning(title='Warning Window',message='Please run the AI model first!', parent=MainPage.Window) #LabelPage.LabelWindows
		elif self.AIResult=='0':
			mWarning=messagebox.showwarning(title='Warning Window',message='There isn\'t any AI model!', parent=MainPage.Window)
		else:
			#Setting Case.Patient(可刪)
			#Case.Patient[8]=self.AIResult
			#Setting Patient Report
			MainPage.C_BIRADS.config(text=self.AIResult)
			
			#Setting Radiobutton
			LabelPage.rC1.deselect()
			LabelPage.rC5.deselect()
			if self.AIResult=='Category 2':
				LabelPage.rC2.select()
				LabelPage.rC3.deselect()
				LabelPage.rC4.deselect()
			elif self.AIResult=='Category 3':
				LabelPage.rC2.deselect()
				LabelPage.rC3.select()
				LabelPage.rC4.deselect()
			elif self.AIResult=='Category 4':
				LabelPage.rC2.deselect()
				LabelPage.rC3.deselect()
				LabelPage.rC4.select()
		return




#Main Function
W=MainWindow()
W.Main_Window_Show()










