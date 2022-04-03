#include<ilcplex/ilocplex.h>
#include<iostream>
#include<math.h>
#include<cstring>
#include<cstdlib>
#include<vector>
#include<deque>
#define  treeBB struct treaBB


using namespace std;
ILOSTLBEGIN


const int n = 4;//nΪ�ܷ���ͻ���
double RB = 10000000;

void getData(int A[][2], int n);//���ڴ��ļ��ж�ȡn���ͻ�����������
void saveCost(int B[][2 * n + 1], const int A[][2], int n);//���ڰ�n���ͻ�����������ת��Ϊ(n+1)*(n+1)���ڽӾ���
double priceProblem_precise(const int graphCost[][2 * n + 1], const double dualValue[], int rem[][n + 1], int roadCost[], const int numVar, vector<vector<vector<int>>> cons);
double masterProblem(const int numVar, const int rem[][n + 1], const int roadCost[], double lamda[], const int A[][2],double var[1000]);
void columnGeration(const int graphCost[][2 * n + 1], const int A[][2]);
int branchPrice(const int graphCost[][2 * n + 1]);
void newNode(treeBB* node1, treeBB* node2, int numVar, double LB, vector<int>* varBound);
int intfinder(int n, vector<double> A);
int ringfounder(int A[][2 * n + 1]);
double columnGeration1(const int graphCost[][2 * n + 1], treeBB* node);
int priceProblemHeuristic(const int graphCost[][2 * n + 1], const double dualValue[], int rem[][2 * n + 1], int roadCost[], const int numVar);
int s = 0;

struct treaBB
{
	int A[1000][2];
	int numVar;
	int rem[1000][2 * n + 1];
	int roadCost[1000];
	double var[1000];
	double LB;
};
void text();
int main()
{
	int temp[n + 1][2];//������ʱ�洢n���ͻ�������
	getData(temp, n);
	temp[0][0] = 150;//��ʼ���������վ��
	temp[0][1] = 150;

	int Cost[2 * n + 1][2 * n + 1];//n���ͻ��ͷ������վ����ڽӾ���
	saveCost(Cost, temp, n);
	for (int i = 0; i <= 2 * n; i++)//�������
	{
		//cout << temp[i][0] <<"        "<< temp[i][1] << endl;
		for (int j = 0; j <= 2 * n; j++)cout << Cost[i][j] << " ";
		cout << "\n";
	}
	//text();
	//columnGeration(Cost, temp);

	branchPrice(Cost);

	//text();
	vector<string>temp1;
	
}
void getData(int A[][2], int n)
{
	FILE* fp = NULL;
	char* line, * record;
	char buffer[1024];
	int count = 1;
	if ((fp = fopen("C:\\Users\\86180\\Desktop\\�½��ļ��� (2)\\odata.csv", "at+")) != NULL)
	{
		fseek(fp, 170L, SEEK_SET);  //��λ���ڶ��У�ÿ��Ӣ���ַ���СΪ1
		char delims[] = ",";
		char* result = NULL;
		int j = 0;
		line = fgets(buffer, sizeof(buffer), fp);
		while ((line) != NULL && count <= n)//��û�ж�ȡ���ļ�ĩβʱѭ������
		{
			record = strtok(line, ",");
			while (record != NULL)//��ȡÿһ�е�����
			{
				if (j == 8)A[count][0] = atoi(record);
				if (j == 9)A[count++][1] = atoi(record);
				if (j == 10)break;  //ֻ���ȡǰ9��

				record = strtok(NULL, ",");
				j++;
			}
			j = 0;
			line = fgets(buffer, sizeof(buffer), fp);
		}
		fclose(fp);
		fp = NULL;
	}
}
void saveCost(int graph[][2 * n + 1], const int A[][2], int n)
{
	for (int i = 0; i <= 2 * n; i++)
	{
		graph[i][i] = 0;

		for (int j = 0; j < i; j++)
		{
			graph[i][j] = abs(A[(i + 1) / 2][(i + 1) % 2] - A[(j + 1) / 2][(j + 1) % 2]);
			graph[j][i] = graph[i][j];
			//cout << graph[i][j] << "  " << i << "  " << endl;
		}


	}
}

double priceProblem_precise(const int graphCost[][2 * n + 1], const double dualValue[], int rem[][2*n + 1], int roadCost[], const int numVar, vector<vector<vector<int>>> cons)
{
	//���˼·��
	//1.�˿���ʼ��һ�������ʼ��������˿ͱ�����
	//2.�˿���ʼ������ǰ���ͻ�Ŀ�ĵ�
	//3.ÿ���ͻ���������һ��

	IloEnv envp;
	IloModel modelp(envp);
	IloNumVarArray varp(envp);
	IloRangeArray conp(envp);
	IloExpr exprp(envp);

	//��ӱ���varp[i*(2*n+1)+j] ����i��j���Ƿ�����·��
	for (int i = 0; i < (2 * n + 1) * (2 * n + 1); i++)varp.add(IloNumVar(envp, 0, 1, ILOINT));

	//���Ŀ�꺯����C
	for (int i = 0; i <= 2 * n; i++)
	{
		for (int j = 0; j <= 2 * n; j++)
		{
			//cout << varp[-1];
			//cout << i << " " << j << " " << i * (2 * n + 1) + j<< varp[i * (2 * n + 1) + j] << endl;
			exprp += (graphCost[i][j]) * varp[i * (2 * n + 1) + j];
		}
	}

	//���Ŀ�꺯�����ɶ�żֵ�����Ĳ���
	for (int i = 1; i <= 2 * n; i ++)
	{
		for (int j = 0; j < 2 * n; j++)
		{
			if (i != j)
				exprp -= dualValue[i - 1] * varp[j * (2 * n + 1) + i];
		}
	}

	IloObjective objp = IloMinimize(envp, exprp);
	IloExprArray diffp;
	diffp = IloExprArray(envp, 3 * n + 2);

	//����ж���·��������ж��ٵ�ʻ����Լ��
	for (int i = 0; i <= 2 * n + 1; i++)
	{

		diffp[i] = IloExpr(envp);

		for (int j = 0; j < 2 * n + 1; j++)
		{
			if (i != 0 && i != 2 * n + 1)
			{

				diffp[i] += (varp[i * (2 * n + 1) + j] - varp[j * (2 * n + 1) + i]);

			}
			else if (i == 0)
			{
				diffp[i] += varp[j];
			}
			else
			{
				diffp[i] += varp[j * (2 * n + 1)];
			}
		}

	}
	for (int i = 0; i <= 2 * n + 1; i++)
	{
		if (i != 0 && i != 2 * n + 1)
			conp.add(diffp[i] == 0);
		else conp.add(diffp[i] == 1);
	}

	//��Ӵ���������������������Ϊ���Լ��
	for (int i = 0; i <= 2 * n; i++)
	{
		conp.add(varp[i * (2 * n + 1) + i] == 0);
	}

	//���ÿ���ͻ���������һ�Σ��˿���ʼ������ǰ���ͻ�Ŀ�ĵص�Լ��
	for (int i = 0; i < n; i++)//���Ƶ�i�б���
	{
		diffp[i + 2 * n + 2] = IloExpr(envp);
		for (int j = 0; j < 2 * n + 1; j++)
		{
			//cout << 2 * i + 1 << "  " << j << endl;
			diffp[i + 2 * n + 2] += varp[j * (2 * n + 1) + 2 * i + 1];
		}
		conp.add(diffp[i + 2 * n + 2] <= 1);
		for (int j = 0; j < 2 * n + 1; j++)
			diffp[i + 2 * n + 2] -= varp[j * (2 * n + 1) + 2 * i + 2];
		//diffp[i + 2 * n + 2] -= varp[(2 * i + 1) * (2 * n + 1) + 2 * i + 2];
		conp.add(diffp[i + 2 * n + 2] == 0);
	}
	IloExprArray diffp2;
	diffp2 = IloExprArray(envp,  n);
	for (int i = 0; i < n; i++)//���Ƶ�i�б���
	{
		diffp2[i] = IloExpr(envp);
		for (int j = 0; j < 2 * n + 1; j++)
		{
			diffp2[i] += varp[j * (2 * n + 1) + 2 * i + 2];
		}
		diffp2[i] -= varp[(2 * i + 1) * (2 * n + 1) + 2 * i + 2];
		conp.add(diffp2[i]==0);
	}
	/*for (int i = 1; i <= 2 * n; i++)
	{
		diffp[i/2 + 2 * n + 2] = IloExpr(envp);
		for (int j = 0; j < 2 * n + 1; j++)
		{
			diffp[i / 2 + 2 * n + 2] += varp[j * (2 * n + 1) + i];
		}
		diffp[i / 2 + 2 * n + 2] -= varp[(2 * n + 1) * i + i];
		conp.add(diffp[i / 2 + 2 * n + 2] == 0);
	}*/
	IloExprArray temp(envp, cons.size());
	for (int i = 0; i < cons.size(); i++)
	{
		temp[i]=IloExpr(envp);
		int sum = 0;
		for (int j = 0; j < cons[i].size(); j++)
		{
			for (int k = 0; k < cons[i][j].size(); k++)
			{
				temp[i] += cons[i][j][k] * varp[j * (2 * n + 1) + k];
				sum += cons[i][j][k];
			}
		}
		//envp.out() << temp[i];
		modelp.add(temp[i] <= sum - 1);
	}
	modelp.add(objp);
	modelp.add(conp);
	IloCplex cplex1(modelp);
	if (!cplex1.solve()) {
		envp.error() << "Failed to optimize LP." << endl;
		exit(-1);
	}
	cout << "\n\n" << cons.size() << "\n\n" << endl;
	int A[2 * n + 1][2 * n + 1];
		
		for (int i = 0; i < 2 * n + 1; i++)
		{
			for (int j = 0; j < 2 * n + 1; j++)
			{
				A[i][j] = cplex1.getValue(varp[i * (2 * n + 1) + j]);
				//cout << A[i][j] << " ";
			}
			//cout << endl;
		}
		if (ringfounder(A) == 0);
		else
		{
			cout <<"\n\nringfounder:"<< ringfounder(A)<<endl;
			//IloExpr temp(envp);
			/*int sum = 0;
			for (int i = 0; i < 2 * n + 1; i++)
			{
				for (int j = 0; j < 2 * n + 1; j++)
				{
					temp += A[i][j] * varp[i * (2 * n + 1) + j];
					sum += A[i][j];
 				}
			}
			cout << temp;*/
			vector<vector<int>> temp2;
			for (int i = 0; i < 2 * n + 1; i++)
			{
				vector<int>temp1;
				for (int j = 0; j < 2 * n + 1; j++)
				{
					temp1.push_back(A[i][j]);
				}
				temp2.push_back(temp1);
			}
			cons.push_back(temp2);
			//modelp.add(temp<=sum-1);
			//envp.out() << modelp;
			//IloCplex cplex1(modelp);
			//cplex1.solve();
			envp.end();
			return priceProblem_precise(graphCost, dualValue, rem, roadCost, numVar, cons);
		}
		cout << "a" << endl;
	
	envp.out() << "b" << endl;
	

	if (cplex1.getObjValue() < 0)
	{
		roadCost[numVar] = 0;
		for (int i = 0; i <= 2 * n; i++)
		{
			for (int j = 0; j <= 2 * n; j++)
			{
				roadCost[numVar] += cplex1.getValue(varp[i * (2 * n + 1) + j]) * graphCost[i][j];
			}
		}
		for (int i = 1; i <= 2 * n; i ++)
		{
			rem[numVar][i - 1] = 0;
			for (int j = 0; j <= 2 * n; j++)
			{
				rem[numVar][i-1] += cplex1.getValue(varp[j * (2 * n + 1) + i]);
			}
		}
		/*for (int i = 0; i <= 2 * n; i++)
		{
			for (int j = 0; j <= 2 * n; j++)
			{
				rema[i][j][s] = cplex1.getValue(varp[i * (2 * n + 1) + j]);
			}
		}*/
		s++;
		
	}
	envp.out() << "c" << endl;
	double x = cplex1.getObjValue();
	//envp.out() << modelp;
	envp.end();
	return x;
}

double masterProblem(const int numVar, const int rem[][2*n + 1], const int roadCost[], double lamda[], const int A[][2], double vap[1000])
{
	IloEnv env;
	IloModel model(env);
	IloNumVarArray var(env);
	IloRangeArray con(env);

	for (int i = 0; i < numVar; i++)var.add(IloNumVar(env, 0, 1));

	IloExpr expr(env);
	for (int i = 0; i < numVar; i++)expr += roadCost[i] * var[i];
	IloObjective obj = IloMinimize(env, expr);

	IloExprArray diff = IloExprArray(env, 2*n);
	for (int i = 0; i < 2*n; i++)
	{
		diff[i] = IloExpr(env);
		for (int j = 0; j < numVar; j++)
		{
			diff[i] += rem[j][i] * var[j];
		}
		con.add(diff[i] >= 1);
	}
	for (int i = 0; i < numVar; i++)
	{
		if (A[i][0] == 1)con.add(var[i] == 1);
		else if (A[i][1] == 0)con.add(var[i] == 0);
	}

	model.add(obj);
	model.add(con);
	IloCplex cplex(model);
	cplex.solve();

	if (!cplex.solve()) {
		env.error() << "Failed to optimize LP." << endl;
		throw(-1);
	}
	else
	{
		cout << "\n\nDUAL" << endl;
		for (int i = 0; i < 2*n; i++)
		{
			lamda[i] = cplex.getDual(con[i]);
			cout << cplex.getDual(con[i]) << " ";
		}
		cout << "\n\nMasterProblem" << endl;
		for (int i = 0; i < numVar; i++)
		{
			
			vap[i] = cplex.getValue(var[i]);
			cout << cplex.getValue(var[i]) << " ";
		}
		cout << endl;
		//env.out() << model;
		return cplex.getObjValue();
	}
	env.end();


}

//�����ɲ��ִ��룬�������һ�����Թ滮���Ž�
//graphCost��¼�����֮������ϵ
//void columnGeration(const int graphCost[][2 * n + 1], const int A[][2])
//{
//	//roadCost��¼ÿһ�д����·�ľ��볤��
//	//rem[i][j]��¼��j���ͻ��Ƿ��ڵ�i����·��
//	//numVar��¼ģ���д��м��ֻ�·
//	//lamda��¼MP�Ķ�ż�����
//
//	int roadCost[1000] = { 0 };
//	int rem[1000][2*n + 1];
//	int numVar;
//	double lamda[2*n + 1] = { 0 };
//	int rema[2 * n + 1][2 * n + 1][1000];
//
//	//��ʼ����һ���⣬�������н��
//	for (int i = 0; i < 2 * n; i++)
//	{
//		roadCost[0] += graphCost[i][i + 1];
//		rem[0][i] = 1;
//	}
//	roadCost[0] += graphCost[2 * n][0];
//	rem[0][2*n] = 1;
//	numVar = 1;
//	double objValue;
//
//	while (1)
//	{
//
//		objValue = masterProblem(numVar, rem, roadCost, lamda, A);
//		cout << "\n\n";
//		for (int i = 0; i < n; i++)cout << lamda[i] << "  ";
//		cout << "\n\n";
//		double reducePrice = priceProblem(graphCost, lamda, rem, roadCost, numVar, rema);
//		if (reducePrice >= -1e-8)break;
//		else numVar += 1;
//		/*for (int j = 0; j <= 2 * n; j++)
//		{
//			for (int k = 0; k <= 2 * n; k++)
//			{
//				cout << rema[j][k][numVar-1] << " ";
//			}
//			cout << endl;
//		}*/
//		cout << endl;
//	}
//	/*for (int i = 0; i < numVar; i++)
//	{
//		for (int j = 0; j < n; j++)
//		{
//			cout << rem[i][j] << "  ";
//		}
//		cout << endl;
//	}*/
//	//for (int i = 0; i < numVar; i++)cout << roadCost[i] << " ";
//	cout << endl;
//	for (int i = 0; i < s; i++)
//	{
//		for (int j = 0; j <= 2 * n; j++)
//		{
//			for (int k = 0; k <= 2 * n; k++)
//			{
//				cout << rema[j][k][i] << " ";
//			}
//			cout << endl;
//		}
//		cout << endl;
//	}
//	cout << objValue;
//}



int ringfounder(int A[][2 * n + 1])
{
	int number = 0;
	int temp[2 * n + 1] = { 0 };
	for (int i = 0; i < 2 * n + 1; i++)
	{
		for (int j = 0; j < 2 * n + 1; j++)
		{
			temp[i] += A[j][i];
		}
	}
	int now = 0;
	do
	{
		temp[now] = 0;
		for (int i = 0; i < 2 * n + 1; i++)
		{
			if (A[now][i] != 0)
			{
				now = i;
				break;
			}
		}
	} while (now != 0);
	int sum = 0;
	for (int i = 0; i < 2 * n + 1; i++)sum += temp[i];
	for (int i = 0; i < 2 * n + 1; i++)
	{
		if (temp[i] == 0)
		{
			for (int j = 0; j < 2 * n + 1; j++)
			{
				A[j][i] = 0;
			}
		}
		
	}
	return sum;
}


int intfinder(int n, double A[])
{
	int index = -1;
	for (int i = 0; i < n; i++)
	{
		if (A[i] >= 1e-8 && (1 - A[i]) >= 1e-8)
		{
			index = i;
			break;
		}
	}
	return index;
}

int branchPrice(const int graphCost[][2 * n + 1])
{
	treeBB* node = new treeBB;
	treeBB* bnode = node;
	node->LB = -1;
	node->numVar = 1;
	node->roadCost[0] = 0;
	for (int i = 0; i < 2 * n; i++)
	{
		node->rem[0][i] = 1;
		node->roadCost[0] += graphCost[i][i + 1];
	}
	node->A[0][0] = 0;
	node->A[0][1] = 1;
	node->var[0] = 1;
	node->rem[0][2 * n] = 1;
	node->roadCost[0] += graphCost[2 * n][0];
	deque<treeBB*> nodes;
	nodes.push_back(node);
	int counter = 0;
	while (1)
	{
		double objValue = columnGeration1(graphCost, node);
		if (intfinder(node->numVar, node->var) == -1)//������
		{
			if (!nodes.empty())
			{
				if (RB > objValue)
				{
					RB = objValue;
					bnode = node;
					for (int i = 0; i < nodes.size(); i++)
					{
						if (nodes.front()->LB >= objValue)
						{
							treeBB* temp = nodes.front();
							nodes.pop_front();
							delete temp;
						}
						else
						{
							nodes.push_back(nodes.front());
							nodes.pop_front();
						}
					}
					if (nodes.empty())
					{
						RB = objValue < RB ? objValue : RB;
						break;
					}
					else
					{
						treeBB* temp = node;
						if (bnode != temp)delete temp;
						node = nodes.front();
						nodes.pop_front();
					}
				}
				else
				{
					treeBB* temp = node;
					if (bnode != temp)delete temp;
					node = nodes.front();
					nodes.pop_front();
				}
				
			}
			else
			{
				if (objValue < RB)
				{
					RB = objValue;
					bnode = node;
				}
				break;
			}	
		}
		else
		{
			int n = intfinder(node->numVar, node->var);
			treeBB*  node1 = new treeBB;
			node1->numVar = node->numVar;
			node1->LB = objValue;
			for (int i = 0; i < node->numVar; i++)
			{
				node1->roadCost[i] = node->roadCost[i];
				node1->A[i][0] = node->A[i][0];
				node1->A[i][1] = node->A[i][1];
				for (int j = 0; i < 2 * n + 1; j++)node1->rem[i][j] = node->rem[i][j];
			}
			treeBB* node2 = new treeBB;
			node2->numVar = node->numVar;
			node2->LB = objValue;
			for (int i = 0; i < node->numVar; i++)
			{
				node2->roadCost[i] = node->roadCost[i];
				node2->A[i][0] = node->A[i][0];
				node2->A[i][1] = node->A[i][1];
				for (int j = 0; i < 2 * n + 1; j++)node2->rem[i][j] = node->rem[i][j];
			}
			node1->A[n][0] = 1;
			node2->A[n][1] = 0;
			nodes.push_back(node1);
			nodes.push_back(node2);
			treeBB* temp = node;
			node = nodes.front();
			if (bnode != temp)delete temp;
			nodes.pop_front();
			counter++;
			cout << "\n\n\nbranch!!!\n\n\n" << counter << "\n\n\n" << endl;
		}
		cout << endl;
	}
	cout << RB<<endl;
	cout << counter<<endl;
	for (int i = 0; i < bnode->numVar; i++)
	{
		for (int j = 0; j < 2 * n + 1; j++)cout << bnode->rem[i][j] << " ";
		cout << endl;
	}
	for (int i = 0; i < bnode->numVar; i++)cout << bnode->var[i];
}

double columnGeration1(const int graphCost[][2 * n + 1],treeBB* node)
{
	cout << "\n\ncolumnGerationP" << endl;
	//roadCost��¼ÿһ�д����·�ľ��볤��
	//rem[i][j]��¼��j���ͻ��Ƿ��ڵ�i����·��
	//numVar��¼ģ���д��м��ֻ�·
	//lamda��¼MP�Ķ�ż�����

	double lamda[2 * n + 1] = { 0 };
	//int rema[2 * n + 1][2 * n + 1][1000];

	//��ʼ����һ���⣬�������н��
	double objValue;
	
	while (1)
	{
		vector<vector<vector<int>>> cons;
		objValue = masterProblem(node->numVar, node->rem, node->roadCost, lamda, node->A,node->var);
		cout << "\n\n";
		for (int i = 0; i < n; i++)cout << lamda[i] << "  ";
		cout << "\n\n";
		double reducePrice = -1;
		//if(priceProblemHeuristic(graphCost,lamda,node->rem,node->roadCost,node->numVar)==-1)
		reducePrice = priceProblem_precise(graphCost, lamda, node->rem, node->roadCost, node->numVar,cons);
		if (reducePrice >= -1e-8)break;
		else
		{
			node->A[node->numVar][0] = 0;
			node->A[node->numVar][1] = 1;
			node->numVar += 1;
		}
	}
	return objValue;
}


int priceProblemHeuristic(const int graphCost[][2 * n + 1], const double dualValue[], int rem[][2 * n + 1], int roadCost[], const int numVar)
{
	int tgrapgCost[2 * n + 1][2 * n + 1],A[2*n+1][2*n+1];
	tgrapgCost[0][0] = 10000;
	A[0][0] = 0;
		for (int j = 1; j < 2 * n + 1; j++)
		{
			tgrapgCost[j][0] = graphCost[j][0];
			A[j][0] = 0;
		}
	for (int i = 1; i < 2 * n + 1; i++)
	{
		for (int j = 0; j < 2 * n + 1; j++)
		{
			tgrapgCost[j][i] = graphCost[j][i] - dualValue[i];
			A[i][j] = 0;
		}
		tgrapgCost[i][i] = 10000;
	}
	int reme[2 * n + 1] = { 0 };
	reme[0] = 1;
	int index = 0;
	int temp_index = 0,temp_value = tgrapgCost[0][0];
	int sum = 0;
	while ((sum + tgrapgCost[index][0]) >= 0)
	{
		temp_value = 10000;
		for (int i = 1; i < 2 * n; i+=2)
		{
			if ((tgrapgCost[index][i]+ tgrapgCost[i][i+1]) < temp_value&&reme[i]!=1)
			{
				temp_value = tgrapgCost[index][i] + tgrapgCost[i][i + 1];
				temp_index = i;
			}
		}
		cout << temp_value << endl;
		if (temp_value == 10000)break;
		A[index][temp_index] = 1;
		A[temp_index][temp_index+1] = 1;
		reme[temp_index] = 1;
		reme[temp_index+1] = 1;
		sum += temp_value;
		index = temp_index+1;
	}
	A[index][0] = 1;
	sum += tgrapgCost[index][0];
	if (ringfounder(A) != 0)return -1;
	if (sum < 0)
	{
		for (int i = 1; i < 2 * n + 1; i++)rem[numVar][i - 1] = reme[i];
		roadCost[numVar] = 0;
		for (int i = 0; i < 2 * n + 1;i++)
		{
			for (int j = 0; j < 2 * n + 1; j++)
			{
				roadCost[numVar] += graphCost[i][j] *A[i][j];
			}
		}
	}
	else return -1;
}